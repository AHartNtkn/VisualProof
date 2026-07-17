import VisualProof.Rule.Structural.SpawnCore

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

/-- If the compiled target items semantically project to the renamed old
items, finishing the spawn scope restricts the fresh local valuation and
projects the entire intrinsic region. -/
theorem spawnNodeRaw_finishRegion_site_projects
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (targetNodup : (target.extend scope).Nodup)
    (sourceItems : ItemSeq signature (source.extend scope).length rels)
    (targetItems : ItemSeq signature (target.extend scope).length rels)
    (hproject : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rawEnv : Fin (target.extend scope).length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteItemSeq model named rawEnv relEnv targetItems →
        denoteItemSeq model named rawEnv relEnv
          (sourceItems.renameWires (embedding.extend scope).index))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin target.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion
          (spawnNodeRaw input node scope portCount port) target scope
          targetItems) →
      denoteRegion model named (outerEnv ∘ embedding.index) relEnv
        (ConcreteElaboration.finishRegion input source scope sourceItems) := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  rintro ⟨localEnv, htarget⟩
  let restrictedLocal :
      Fin (ConcreteElaboration.exactScopeWires input scope).length →
        model.Carrier :=
    fun localWire => localEnv
      (Fin.cast
        (spawnNodeRaw_exactScopeWires_length_at_scope input node scope
          portCount port).symm
        (Fin.castAdd portCount localWire))
  refine ⟨restrictedLocal, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at htarget ⊢
  have htargetRaw := (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend target scope))
    (extendWireEnv outerEnv localEnv) relEnv targetItems).1 htarget
  have holdRenamed := hproject model named _ relEnv htargetRaw
  have holdRaw := (denoteItemSeq_renameWires model named
    (embedding.extend scope).index
    ((extendWireEnv outerEnv localEnv) ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend target scope))
    relEnv sourceItems).1 holdRenamed
  apply (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend source scope))
    (extendWireEnv (outerEnv ∘ embedding.index) restrictedLocal)
    relEnv sourceItems).2
  have hembedding : (embedding.extend scope).index =
      spawnNodeRaw_extendedWireMapAtScope embedding := by
    funext index
    exact SpawnContextEmbedding.extend_index_eq_map_at_scope embedding
      targetNodup index
  rw [hembedding] at holdRaw
  have henv := spawnNodeRaw_extendWireEnv_at_scope input node scope portCount
    port source target embedding outerEnv localEnv
  change ((extendWireEnv outerEnv localEnv ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend target scope)) ∘
      spawnNodeRaw_extendedWireMapAtScope embedding) =
    (extendWireEnv (outerEnv ∘ embedding.index) restrictedLocal ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend source scope))
    at henv
  rw [henv] at holdRaw
  exact holdRaw

/-- Reverse counterpart of `spawnNodeRaw_finishRegion_site_projects`.  A
valuation of the fresh local wires extends the source witness, while the
caller proves that the renamed old frame plus the fresh occurrence denotes
the compiled target items. -/
def spawnNodeRaw_freshExtendedIndex
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (fresh : Fin portCount) : Fin (target.extend scope).length :=
  Fin.cast
    (ConcreteElaboration.WireContext.length_extend target scope).symm
    (Fin.natAdd target.length
      (Fin.cast
        (spawnNodeRaw_exactScopeWires_length_at_scope input node scope
          portCount port).symm
        (Fin.natAdd
          (ConcreteElaboration.exactScopeWires input scope).length fresh)))

theorem spawnNodeRaw_freshExtendedIndex_get
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (fresh : Fin portCount) :
    (target.extend scope).get
        (spawnNodeRaw_freshExtendedIndex input node scope portCount port target
          fresh) =
      Fin.natAdd input.wireCount fresh := by
  have hvalid : target.length +
      (ConcreteElaboration.exactScopeWires input scope).length + fresh.val <
      (target ++ ConcreteElaboration.exactScopeWires
        (spawnNodeRaw input node scope portCount port) scope).length := by
    rw [List.length_append,
      spawnNodeRaw_exactScopeWires_length_at_scope]
    omega
  let listIndex : Fin (target ++ ConcreteElaboration.exactScopeWires
      (spawnNodeRaw input node scope portCount port) scope).length :=
    ⟨target.length +
        (ConcreteElaboration.exactScopeWires input scope).length +
          fresh.val, hvalid⟩
  have hindex : spawnNodeRaw_freshExtendedIndex input node scope portCount port
      target fresh = listIndex := by
    apply Fin.ext
    simp [spawnNodeRaw_freshExtendedIndex, listIndex]
    omega
  rw [hindex]
  change (target ++ ConcreteElaboration.exactScopeWires
      (spawnNodeRaw input node scope portCount port) scope).get listIndex = _
  simp only [List.get_eq_getElem]
  dsimp only [listIndex]
  rw [List.getElem_append_right (by omega)]
  simp only [spawnNodeRaw_exactScopeWires, if_pos]
  simp only [show target.length +
      (ConcreteElaboration.exactScopeWires input scope).length + fresh.val -
        target.length =
      (ConcreteElaboration.exactScopeWires input scope).length + fresh.val by
        omega]
  refine (List.getElem_append_right (as :=
      List.map (Fin.castAdd portCount)
        (ConcreteElaboration.exactScopeWires input scope))
      (bs := List.map (Fin.natAdd input.wireCount) (allFin portCount))
      (i := (ConcreteElaboration.exactScopeWires input scope).length +
        fresh.val) (by simp)).trans ?_
  simp [allFin_eq_finRange]

theorem spawnNodeRaw_finishRegion_site_reflects
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (targetNodup : (target.extend scope).Nodup)
    (sourceItems : ItemSeq signature (source.extend scope).length rels)
    (targetItems : ItemSeq signature (target.extend scope).length rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin target.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (freshValues : Fin portCount → model.Carrier)
    (hreflect : ∀ (rawEnv : Fin (target.extend scope).length → model.Carrier),
      (∀ fresh : Fin portCount,
        rawEnv (spawnNodeRaw_freshExtendedIndex input node scope portCount port
          target fresh) = freshValues fresh) →
      denoteItemSeq model named rawEnv relEnv
          (sourceItems.renameWires (embedding.extend scope).index) →
        denoteItemSeq model named rawEnv relEnv targetItems) :
    denoteRegion model named (outerEnv ∘ embedding.index) relEnv
        (ConcreteElaboration.finishRegion input source scope sourceItems) →
      denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion
          (spawnNodeRaw input node scope portCount port) target scope
          targetItems) := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  rintro ⟨sourceLocal, hsource⟩
  let targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (spawnNodeRaw input node scope portCount port) scope).length →
      model.Carrier := fun index =>
    Fin.addCases sourceLocal freshValues
      (Fin.cast
        (spawnNodeRaw_exactScopeWires_length_at_scope input node scope
          portCount port) index)
  refine ⟨targetLocal, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at hsource ⊢
  have hsourceRaw := (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend source scope))
    (extendWireEnv (outerEnv ∘ embedding.index) sourceLocal) relEnv
    sourceItems).1 hsource
  have henv := spawnNodeRaw_extendWireEnv_at_scope input node scope portCount
    port source target embedding outerEnv targetLocal
  have hlocal : (fun localWire => targetLocal
      (Fin.cast
        (spawnNodeRaw_exactScopeWires_length_at_scope input node scope
          portCount port).symm
        (Fin.castAdd portCount localWire))) = sourceLocal := by
    funext localWire
    simp [targetLocal]
  rw [hlocal] at henv
  have hindex : (embedding.extend scope).index =
      spawnNodeRaw_extendedWireMapAtScope embedding := by
    funext index
    exact SpawnContextEmbedding.extend_index_eq_map_at_scope embedding
      targetNodup index
  have henv' : ((extendWireEnv outerEnv targetLocal ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend target scope)) ∘
      (embedding.extend scope).index) =
    (extendWireEnv (outerEnv ∘ embedding.index) sourceLocal ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend source scope)) := by
    rw [hindex]
    exact henv
  have hrenamed := (denoteItemSeq_renameWires model named
    (embedding.extend scope).index
    ((extendWireEnv outerEnv targetLocal) ∘
      Fin.cast (ConcreteElaboration.WireContext.length_extend target scope))
    relEnv sourceItems).2 ((congrArg
      (fun current => denoteItemSeq model named current relEnv sourceItems)
      henv').mpr hsourceRaw)
  have hfresh : ∀ fresh : Fin portCount,
      ((extendWireEnv outerEnv targetLocal) ∘
        Fin.cast (ConcreteElaboration.WireContext.length_extend target scope))
          (spawnNodeRaw_freshExtendedIndex input node scope portCount port target
            fresh) = freshValues fresh := by
    intro fresh
    simp [spawnNodeRaw_freshExtendedIndex, extendWireEnv, targetLocal]
  have htargetRaw := hreflect _ hfresh hrenamed
  exact (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend target scope))
    (extendWireEnv outerEnv targetLocal) relEnv targetItems).2 htargetRaw

/-- The open-root finishing kernel projects a root spawn to the source root
under the preserved external-class ordering and restricted hidden valuation. -/
theorem spawnNodeRaw_finishRoot_site_projects
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (sourceItems : ItemSeq signature source.rootWires.length [])
    (targetItems : ItemSeq signature
      (spawnNodeRawOpen source node scope portCount port).rootWires.length [])
    (hproject : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rawEnv : Fin
        (spawnNodeRawOpen source node scope portCount port).rootWires.length →
          model.Carrier),
      denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit targetItems →
        denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit
          (sourceItems.renameWires
            (spawnNodeRawOpenRootEmbedding source node scope portCount port
              hroot).index))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).exposedWires.length →
        model.Carrier) :
    denoteRegion (relCtx := []) model named outerEnv PUnit.unit
        (ConcreteElaboration.finishRoot
          (spawnNodeRawOpen source node scope portCount port).exposedWires
          (spawnNodeRawOpen source node scope portCount port).hiddenWires
          targetItems) →
      denoteRegion (relCtx := []) model named
        (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount
          port) PUnit.unit
        (ConcreteElaboration.finishRoot source.exposedWires source.hiddenWires
          sourceItems) := by
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  rintro ⟨localEnv, htarget⟩
  let restrictedLocal : Fin source.hiddenWires.length → model.Carrier :=
    fun hidden => localEnv
      (spawnNodeRawOpenHiddenIndex source node scope portCount port hroot hidden)
  refine ⟨restrictedLocal, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at htarget ⊢
  have htargetRaw := (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append
      (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
      (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    (extendWireEnv outerEnv localEnv) PUnit.unit targetItems).1 htarget
  have holdRenamed := hproject model named _ htargetRaw
  have holdRaw := (denoteItemSeq_renameWires (relCtx := []) model named
    (spawnNodeRawOpenRootEmbedding source node scope portCount port hroot).index
    ((extendWireEnv outerEnv localEnv) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    PUnit.unit sourceItems).1 holdRenamed
  apply (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append (as := source.exposedWires)
      (bs := source.hiddenWires)))
    (extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      restrictedLocal) PUnit.unit sourceItems).2
  have henv := spawnNodeRaw_rootExtendWireEnv source node scope portCount port
    hroot model.Carrier outerEnv localEnv
  change (((extendWireEnv outerEnv localEnv) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires))) ∘
      (spawnNodeRawOpenRootEmbedding source node scope portCount port
        hroot).index) =
    ((extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      restrictedLocal) ∘
      Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires))) at henv
  exact (congrArg
    (fun current => denoteItemSeq (relCtx := []) model named current
      PUnit.unit sourceItems) henv).mp holdRaw

/-- At a non-root spawn the root exposed/hidden split has identical positional
shape.  Any implication between the compiled target frame and the renamed old
frame therefore lifts directly through `finishRoot`. -/
theorem spawnNodeRaw_finishRoot_away_projects
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hne : source.diagram.root ≠ scope)
    (sourceItems : ItemSeq signature source.rootWires.length [])
    (targetItems : ItemSeq signature
      (spawnNodeRawOpen source node scope portCount port).rootWires.length [])
    (hproject : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rawEnv : Fin
        (spawnNodeRawOpen source node scope portCount port).rootWires.length →
          model.Carrier),
      denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit targetItems →
        denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit
          (sourceItems.renameWires
            (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
              hne).index))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).exposedWires.length →
        model.Carrier) :
    denoteRegion (relCtx := []) model named outerEnv PUnit.unit
        (ConcreteElaboration.finishRoot
          (spawnNodeRawOpen source node scope portCount port).exposedWires
          (spawnNodeRawOpen source node scope portCount port).hiddenWires
          targetItems) →
      denoteRegion (relCtx := []) model named
        (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount
          port) PUnit.unit
        (ConcreteElaboration.finishRoot source.exposedWires source.hiddenWires
          sourceItems) := by
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  rintro ⟨localEnv, htarget⟩
  let hiddenLength :
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length =
        source.hiddenWires.length := by
    rw [spawnNodeRawOpen_hiddenWires, if_neg hne, List.append_nil]
    exact List.length_map _
  let sourceLocal : Fin source.hiddenWires.length → model.Carrier :=
    localEnv ∘ Fin.cast hiddenLength.symm
  refine ⟨sourceLocal, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at htarget ⊢
  have htargetRaw := (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append
      (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
      (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    (extendWireEnv outerEnv localEnv) PUnit.unit targetItems).1 htarget
  have holdRenamed := hproject model named _ htargetRaw
  have holdRaw := (denoteItemSeq_renameWires (relCtx := []) model named
    (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
      hne).index
    ((extendWireEnv outerEnv localEnv) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    PUnit.unit sourceItems).1 holdRenamed
  apply (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append (as := source.exposedWires)
      (bs := source.hiddenWires)))
    (extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      sourceLocal) PUnit.unit sourceItems).2
  have henv := spawnNodeRaw_rootExtendWireEnvAway source node scope portCount
    port hne model.Carrier outerEnv localEnv
  change (((extendWireEnv outerEnv localEnv) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires))) ∘
      (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
        hne).index) =
    ((extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      sourceLocal) ∘
      Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires))) at henv
  exact (congrArg
    (fun current => denoteItemSeq (relCtx := []) model named current
      PUnit.unit sourceItems) henv).mp holdRaw

theorem spawnNodeRaw_finishRoot_away_reflects
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hne : source.diagram.root ≠ scope)
    (sourceItems : ItemSeq signature source.rootWires.length [])
    (targetItems : ItemSeq signature
      (spawnNodeRawOpen source node scope portCount port).rootWires.length [])
    (hproject : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rawEnv : Fin
        (spawnNodeRawOpen source node scope portCount port).rootWires.length →
          model.Carrier),
      denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit
          (sourceItems.renameWires
            (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
              hne).index) →
        denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).exposedWires.length →
        model.Carrier) :
    denoteRegion (relCtx := []) model named
        (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount
          port) PUnit.unit
        (ConcreteElaboration.finishRoot source.exposedWires source.hiddenWires
          sourceItems) →
      denoteRegion (relCtx := []) model named outerEnv PUnit.unit
        (ConcreteElaboration.finishRoot
          (spawnNodeRawOpen source node scope portCount port).exposedWires
          (spawnNodeRawOpen source node scope portCount port).hiddenWires
          targetItems) := by
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  rintro ⟨sourceLocal, hsource⟩
  let hiddenLength :
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length =
        source.hiddenWires.length := by
    rw [spawnNodeRawOpen_hiddenWires, if_neg hne, List.append_nil]
    exact List.length_map _
  let targetLocal : Fin
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length →
        model.Carrier := sourceLocal ∘ Fin.cast hiddenLength
  refine ⟨targetLocal, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at hsource ⊢
  have hsourceRaw := (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append (as := source.exposedWires)
      (bs := source.hiddenWires)))
    (extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      sourceLocal) PUnit.unit sourceItems).1 hsource
  have henv := spawnNodeRaw_rootExtendWireEnvAway source node scope portCount
    port hne model.Carrier outerEnv targetLocal
  have hlocal : targetLocal ∘ Fin.cast hiddenLength.symm = sourceLocal := by
    funext index
    apply congrArg sourceLocal
    rfl
  change (((extendWireEnv outerEnv targetLocal) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires))) ∘
      (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
        hne).index) =
    ((extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      (targetLocal ∘ Fin.cast hiddenLength.symm)) ∘
      Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires))) at henv
  rw [hlocal] at henv
  rw [← henv] at hsourceRaw
  have hrenamed := (denoteItemSeq_renameWires (relCtx := []) model named
    (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
      hne).index
    ((extendWireEnv outerEnv targetLocal) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    PUnit.unit sourceItems).2 hsourceRaw
  have htargetRaw := hproject model named _ hrenamed
  exact (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append
      (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
      (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    (extendWireEnv outerEnv targetLocal) PUnit.unit targetItems).2 htargetRaw

/-- Successful compilation at the spawn scope projects semantically to the
source region.  The proof follows the compiler's actual traversal order,
discards the fresh-node conjunct, and restricts the fresh local valuations. -/
theorem spawnNodeRaw_compileRegion_site_projects
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend scope).Exact scope)
    (htargetExact : (target.extend scope).Exact scope)
    (sourceBody : Region signature source.length rels)
    (targetBody : Region signature target.length rels)
    (hsourceBody : ConcreteElaboration.compileRegion? signature input
      (fuel + 1) scope source binders = some sourceBody)
    (htargetBody : ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port)
      (fuel + 1) scope target binders = some targetBody) :
    ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin target.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model named outerEnv relEnv targetBody →
        denoteRegion model named (outerEnv ∘ embedding.index) relEnv
          sourceBody := by
  let sourceNodes :=
    (filterFin fun old => decide ((input.nodes old).region = scope)).map
      (fun old => ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) old)
  let sourceChildren :=
    (filterFin fun child =>
      decide ((input.regions child).parent? = some scope)).map
      (ConcreteElaboration.LocalOccurrence.child (nodes := input.nodeCount))
  let targetNodes := sourceNodes.map (spawnNodeRaw_oldOccurrence input)
  let targetChildren := sourceChildren.map (spawnNodeRaw_oldOccurrence input)
  let fresh := [ConcreteElaboration.LocalOccurrence.node
    (regions := input.regionCount) (Fin.last input.nodeCount)]
  have hsourceOccurrences :
      ConcreteElaboration.localOccurrences input scope =
        sourceNodes ++ sourceChildren := by
    rfl
  have htargetOccurrences :
      ConcreteElaboration.localOccurrences
          (spawnNodeRaw input node scope portCount port) scope =
        targetNodes ++ fresh ++ targetChildren := by
    rw [spawnNodeRaw_localOccurrences, if_pos hnode]
    simp only [sourceNodes, sourceChildren, targetNodes, targetChildren, fresh,
      List.map_map]
    rfl
  simp only [ConcreteElaboration.compileRegion?] at hsourceBody htargetBody
  cases hsourceItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
      input (ConcreteElaboration.compileRegion? signature input fuel)
      (source.extend scope) binders
      (ConcreteElaboration.localOccurrences input scope) with
  | none => simp [hsourceItemsEq] at hsourceBody
  | some sourceItems =>
    simp [hsourceItemsEq] at hsourceBody
    subst sourceBody
    cases htargetItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        (target.extend scope) binders
        (ConcreteElaboration.localOccurrences
          (spawnNodeRaw input node scope portCount port) scope) with
    | none => simp [htargetItemsEq] at htargetBody
    | some targetItems =>
      simp [htargetItemsEq] at htargetBody
      subst targetBody
      have htargetOrdered :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port) fuel)
              (target.extend scope) binders
              (targetNodes ++ (fresh ++ targetChildren)) =
            some targetItems := by
        rw [← List.append_assoc, ← htargetOccurrences]
        exact htargetItemsEq
      obtain ⟨nodeItems, restItems, hnodeItems, hrestItems,
          htargetItems⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input node scope portCount port) fuel)
          (target.extend scope) binders targetNodes
          (fresh ++ targetChildren) targetItems htargetOrdered
      obtain ⟨freshItems, childItems, hfreshItems, hchildItems,
          hrestItemsEq⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input node scope portCount port) fuel)
          (target.extend scope) binders fresh targetChildren restItems hrestItems
      have holdCompile :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port) fuel)
              (target.extend scope) binders
              ((ConcreteElaboration.localOccurrences input scope).map
                (spawnNodeRaw_oldOccurrence input)) =
            some (nodeItems.append childItems) := by
        rw [hsourceOccurrences, List.map_append]
        change ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node scope portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node scope portCount port) fuel)
            (target.extend scope) binders (targetNodes ++ targetChildren) = _
        exact ConcreteElaboration.compileOccurrencesWith?_append
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input node scope portCount port) fuel)
          (target.extend scope) binders targetNodes targetChildren nodeItems
          childItems hnodeItems hchildItems
      have holdMap := spawnNodeRaw_compileOldOccurrencesAtSite input node scope
        portCount port hinput htarget hnode fuel source target embedding binders
        hsourceExact htargetExact
      rw [hsourceItemsEq] at holdMap
      simp only [Option.map_some] at holdMap
      rw [holdCompile] at holdMap
      have holdItems : nodeItems.append childItems =
          sourceItems.renameWires (embedding.extend scope).index :=
        Option.some.inj holdMap
      intro model named outerEnv relEnv hdenotes
      refine spawnNodeRaw_finishRegion_site_projects input node scope portCount
        port source target embedding htargetExact.nodup sourceItems targetItems
        ?_ model named outerEnv relEnv hdenotes
      intro currentModel currentNamed rawEnv currentRelEnv htargetDenotes
      rw [htargetItems, hrestItemsEq] at htargetDenotes
      rw [denoteItemSeq_append] at htargetDenotes
      rcases htargetDenotes with ⟨hnodeDenotes, hrestDenotes⟩
      rw [denoteItemSeq_append] at hrestDenotes
      rcases hrestDenotes with ⟨_, hchildDenotes⟩
      rw [← holdItems]
      exact (denoteItemSeq_append currentModel currentNamed rawEnv currentRelEnv
        nodeItems childItems).2 ⟨hnodeDenotes, hchildDenotes⟩

/-- Successful open-root compilation at a root spawn projects to the source
open root.  This is distinct from the nested-region kernel because the sole
compiler uses `finishRoot` and its exposed/hidden partition at the sheet. -/
theorem spawnNodeRaw_compileRoot_site_projects
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hnode : node.region = scope)
    (hroot : source.val.diagram.root = scope)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature)
    (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length
      [])
    (hsourceBody : ConcreteElaboration.compileRoot? signature
      source.val.diagram source.val.exposedWires source.val.hiddenWires =
        some sourceBody)
    (htargetBody : ConcreteElaboration.compileRoot? signature
      (spawnNodeRaw source.val.diagram node scope portCount port)
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires
      (spawnNodeRawOpen source.val node scope portCount port).hiddenWires =
        some targetBody) :
    ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody →
        denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody := by
  let input := source.val.diagram
  let targetOpen := spawnNodeRawOpen source.val node scope portCount port
  let sourceNodes :=
    (filterFin fun old => decide ((input.nodes old).region = input.root)).map
      (fun old => ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) old)
  let sourceChildren :=
    (filterFin fun child =>
      decide ((input.regions child).parent? = some input.root)).map
      (ConcreteElaboration.LocalOccurrence.child (nodes := input.nodeCount))
  let targetNodes := sourceNodes.map (spawnNodeRaw_oldOccurrence input)
  let targetChildren := sourceChildren.map (spawnNodeRaw_oldOccurrence input)
  let fresh := [ConcreteElaboration.LocalOccurrence.node
    (regions := input.regionCount) (Fin.last input.nodeCount)]
  have hnodeRoot : node.region = input.root := hnode.trans hroot.symm
  have hsourceOccurrences :
      ConcreteElaboration.localOccurrences input input.root =
        sourceNodes ++ sourceChildren := by
    rfl
  have htargetOccurrences :
      ConcreteElaboration.localOccurrences targetOpen.diagram input.root =
        targetNodes ++ fresh ++ targetChildren := by
    change ConcreteElaboration.localOccurrences
      (spawnNodeRaw input node scope portCount port) input.root = _
    rw [spawnNodeRaw_localOccurrences, if_pos hnodeRoot]
    simp only [input, sourceNodes, sourceChildren, targetNodes,
      targetChildren, fresh, List.map_map]
    rfl
  change ConcreteElaboration.compileRoot? signature input
      source.val.exposedWires source.val.hiddenWires = some sourceBody
    at hsourceBody
  change ConcreteElaboration.compileRoot? signature targetOpen.diagram
      targetOpen.exposedWires targetOpen.hiddenWires = some targetBody
    at htargetBody
  simp only [ConcreteElaboration.compileRoot?] at hsourceBody htargetBody
  cases hsourceItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
      input (ConcreteElaboration.compileRegion? signature input input.regionCount)
      (source.val.exposedWires ++ source.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input input.root) with
  | none => simp [hsourceItemsEq] at hsourceBody
  | some sourceItems =>
    simp [hsourceItemsEq] at hsourceBody
    subst sourceBody
    cases htargetItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
        targetOpen.diagram
        (ConcreteElaboration.compileRegion? signature targetOpen.diagram
          targetOpen.diagram.regionCount)
        (targetOpen.exposedWires ++ targetOpen.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences targetOpen.diagram
          targetOpen.diagram.root) with
    | none => simp [input, targetOpen, htargetItemsEq] at htargetBody
    | some targetItems =>
      simp [input, targetOpen, htargetItemsEq] at htargetBody
      subst targetBody
      have htargetOrdered :
          ConcreteElaboration.compileOccurrencesWith? signature
              targetOpen.diagram
              (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                input.regionCount)
              targetOpen.rootWires ConcreteElaboration.BinderContext.empty
              (targetNodes ++ (fresh ++ targetChildren)) = some targetItems := by
        rw [← List.append_assoc, ← htargetOccurrences]
        exact htargetItemsEq
      obtain ⟨nodeItems, restItems, hnodeItems, hrestItems,
          htargetItems⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount)
          targetOpen.rootWires ConcreteElaboration.BinderContext.empty
          targetNodes (fresh ++ targetChildren) targetItems htargetOrdered
      obtain ⟨freshItems, childItems, hfreshItems, hchildItems,
          hrestItemsEq⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount)
          targetOpen.rootWires ConcreteElaboration.BinderContext.empty
          fresh targetChildren restItems hrestItems
      have holdCompile :
          ConcreteElaboration.compileOccurrencesWith? signature
              targetOpen.diagram
              (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                input.regionCount)
              targetOpen.rootWires ConcreteElaboration.BinderContext.empty
              ((ConcreteElaboration.localOccurrences input input.root).map
                (spawnNodeRaw_oldOccurrence input)) =
            some (nodeItems.append childItems) := by
        rw [hsourceOccurrences, List.map_append]
        change ConcreteElaboration.compileOccurrencesWith? signature
            targetOpen.diagram
            (ConcreteElaboration.compileRegion? signature targetOpen.diagram
              input.regionCount)
            targetOpen.rootWires ConcreteElaboration.BinderContext.empty
            (targetNodes ++ targetChildren) = _
        exact ConcreteElaboration.compileOccurrencesWith?_append
          (ConcreteElaboration.compileRegion? signature targetOpen.diagram
            input.regionCount)
          targetOpen.rootWires ConcreteElaboration.BinderContext.empty
          targetNodes targetChildren nodeItems childItems hnodeItems hchildItems
      let embedding := spawnNodeRawOpenRootEmbedding source.val node scope
        portCount port hroot
      have holdMap := spawnNodeRaw_compileOldOccurrencesAtRoot input node scope
        portCount port source.property.diagram_well_formed htarget hnode hroot
        input.regionCount source.val.rootWires targetOpen.rootWires embedding
        ConcreteElaboration.BinderContext.empty
        (OpenConcreteDiagram.rootWires_exact source.val source.property)
        (OpenConcreteDiagram.rootWires_exact targetOpen
          (spawnNodeRawOpen_wellFormed source node scope portCount port htarget))
      have hsourceItemsRoot :
          ConcreteElaboration.compileOccurrencesWith? signature input
              (ConcreteElaboration.compileRegion? signature input
                input.regionCount)
              source.val.rootWires ConcreteElaboration.BinderContext.empty
              (ConcreteElaboration.localOccurrences input input.root) =
            some sourceItems := by
        exact hsourceItemsEq
      rw [hsourceItemsRoot] at holdMap
      have holdCompileRaw :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port)
                input.regionCount)
              targetOpen.rootWires ConcreteElaboration.BinderContext.empty
              ((ConcreteElaboration.localOccurrences input input.root).map
                (spawnNodeRaw_oldOccurrence input)) =
            some (nodeItems.append childItems) := by
        exact holdCompile
      have hmapped : some (nodeItems.append childItems) =
          Option.map (ItemSeq.renameWires embedding.index) (some sourceItems) :=
        holdCompileRaw.symm.trans holdMap
      have holdItems : nodeItems.append childItems =
          sourceItems.renameWires embedding.index := by
        exact Option.some.inj hmapped
      intro model named outerEnv hdenotes
      refine spawnNodeRaw_finishRoot_site_projects source.val node scope
        portCount port hroot sourceItems targetItems ?_ model named outerEnv
        hdenotes
      intro currentModel currentNamed rawEnv htargetDenotes
      rw [htargetItems, hrestItemsEq] at htargetDenotes
      rw [denoteItemSeq_append] at htargetDenotes
      rcases htargetDenotes with ⟨hnodeDenotes, hrestDenotes⟩
      rw [denoteItemSeq_append] at hrestDenotes
      rcases hrestDenotes with ⟨_, hchildDenotes⟩
      have holdItemsExplicit : nodeItems.append childItems =
          sourceItems.renameWires
            (spawnNodeRawOpenRootEmbedding source.val node scope portCount port
              hroot).index := by
        exact holdItems
      have holdDenotes :=
        (denoteItemSeq_append (relCtx := []) currentModel currentNamed rawEnv
          PUnit.unit nodeItems childItems).2 ⟨hnodeDenotes, hchildDenotes⟩
      exact (congrArg
        (fun items => denoteItemSeq (relCtx := []) currentModel currentNamed
          rawEnv PUnit.unit items) holdItemsExplicit).mp holdDenotes

/-- Reverse root-site finishing kernel.  Fresh root-scope wires are hidden,
so extending the source hidden valuation with caller-chosen witnesses yields
the target root valuation. -/
def spawnNodeRawOpenFreshRootIndex
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (hroot : source.diagram.root = scope)
    (fresh : Fin portCount) :
    Fin (spawnNodeRawOpen source node scope portCount port).rootWires.length :=
  Fin.cast (by
    have hlist := spawnNodeRawOpen_rootWires source node scope portCount port
    rw [if_pos hroot] at hlist
    calc
      source.rootWires.length + portCount =
          (source.rootWires.map (Fin.castAdd portCount) ++
            (allFin portCount).map
              (Fin.natAdd source.diagram.wireCount)).length := by
        simp [allFin_eq_finRange]
      _ = (spawnNodeRawOpen source node scope portCount port).rootWires.length :=
        (congrArg List.length hlist).symm)
    (Fin.natAdd source.rootWires.length fresh)

theorem spawnNodeRawOpenFreshRootIndex_get
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (hroot : source.diagram.root = scope)
    (fresh : Fin portCount) :
    (spawnNodeRawOpen source node scope portCount port).rootWires.get
        (spawnNodeRawOpenFreshRootIndex source node scope portCount port hroot
          fresh) =
      Fin.natAdd source.diagram.wireCount fresh := by
  let target := spawnNodeRawOpen source node scope portCount port
  let suffix := (allFin portCount).map
    (Fin.natAdd source.diagram.wireCount)
  have heq : target.rootWires =
      source.rootWires.map (Fin.castAdd portCount) ++ suffix := by
    simpa only [suffix, if_pos hroot] using
      spawnNodeRawOpen_rootWires source node scope portCount port
  have hindex :
      spawnNodeRawOpenFreshRootIndex source node scope portCount port hroot
          fresh =
        Fin.cast (congrArg List.length heq).symm
          (Fin.cast (List.length_append
            (as := source.rootWires.map (Fin.castAdd portCount))
            (bs := suffix)).symm
            (Fin.natAdd (source.rootWires.map
              (Fin.castAdd portCount)).length
              (Fin.cast (by
                change portCount = suffix.length
                simp [suffix, allFin_eq_finRange]) fresh))) := by
    apply Fin.ext
    simp [spawnNodeRawOpenFreshRootIndex]
  rw [hindex]
  let sourceIndex : Fin
      (source.rootWires.map (Fin.castAdd portCount) ++ suffix).length :=
    Fin.cast (List.length_append
      (as := source.rootWires.map (Fin.castAdd portCount))
      (bs := suffix)).symm
      (Fin.natAdd (source.rootWires.map
        (Fin.castAdd portCount)).length
        (Fin.cast (by
          change portCount = suffix.length
          simp [suffix, allFin_eq_finRange]) fresh))
  refine (get_of_eq heq sourceIndex).trans ?_
  have hvalid : source.rootWires.length + fresh.val <
      (source.rootWires.map (Fin.castAdd portCount) ++
        (allFin portCount).map
          (Fin.natAdd source.diagram.wireCount)).length := by
    simp [allFin_eq_finRange]
  let listIndex : Fin (source.rootWires.map (Fin.castAdd portCount) ++
      (allFin portCount).map
        (Fin.natAdd source.diagram.wireCount)).length :=
    ⟨source.rootWires.length + fresh.val, hvalid⟩
  have hlistIndex : sourceIndex = listIndex := by
    apply Fin.ext
    simp [sourceIndex, listIndex]
  rw [hlistIndex]
  change (source.rootWires.map (Fin.castAdd portCount) ++
      (allFin portCount).map
        (Fin.natAdd source.diagram.wireCount)).get listIndex = _
  simp only [List.get_eq_getElem]
  dsimp only [listIndex]
  rw [List.getElem_append_right (by simp)]
  simp [allFin_eq_finRange]

theorem spawnNodeRaw_finishRoot_site_reflects
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (sourceItems : ItemSeq signature source.rootWires.length [])
    (targetItems : ItemSeq signature
      (spawnNodeRawOpen source node scope portCount port).rootWires.length [])
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).exposedWires.length →
        model.Carrier)
    (freshValues : Fin portCount → model.Carrier)
    (hreflect : ∀ (rawEnv : Fin
        (spawnNodeRawOpen source node scope portCount port).rootWires.length →
          model.Carrier),
      (∀ fresh : Fin portCount,
        rawEnv (spawnNodeRawOpenFreshRootIndex source node scope portCount port
          hroot fresh) = freshValues fresh) →
      denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit
          (sourceItems.renameWires
            (spawnNodeRawOpenRootEmbedding source node scope portCount port
              hroot).index) →
        denoteItemSeq (relCtx := []) model named rawEnv PUnit.unit targetItems) :
    denoteRegion (relCtx := []) model named
        (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount
          port) PUnit.unit
        (ConcreteElaboration.finishRoot source.exposedWires source.hiddenWires
          sourceItems) →
      denoteRegion (relCtx := []) model named outerEnv PUnit.unit
        (ConcreteElaboration.finishRoot
          (spawnNodeRawOpen source node scope portCount port).exposedWires
          (spawnNodeRawOpen source node scope portCount port).hiddenWires
          targetItems) := by
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  rintro ⟨sourceLocal, hsource⟩
  let hiddenLength :
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length =
        source.hiddenWires.length + portCount := by
    rw [spawnNodeRawOpen_hiddenWires, if_pos hroot]
    calc
      (source.hiddenWires.map (Fin.castAdd portCount) ++
          (allFin portCount).map
            (Fin.natAdd source.diagram.wireCount)).length =
        (source.hiddenWires.map (Fin.castAdd portCount)).length +
          ((allFin portCount).map
            (Fin.natAdd source.diagram.wireCount)).length :=
              List.length_append
      _ = source.hiddenWires.length + portCount := by
        rw [List.length_map, List.length_map, allFin_eq_finRange,
          List.length_finRange]
  let targetLocal : Fin
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length →
        model.Carrier := fun index =>
    Fin.addCases sourceLocal freshValues (Fin.cast hiddenLength index)
  refine ⟨targetLocal, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at hsource ⊢
  have hsourceRaw := (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append (as := source.exposedWires)
      (bs := source.hiddenWires)))
    (extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount
        port) sourceLocal) PUnit.unit sourceItems).1 hsource
  have henv := spawnNodeRaw_rootExtendWireEnv source node scope portCount port
    hroot model.Carrier outerEnv targetLocal
  have hlocal : (fun index => targetLocal
      (spawnNodeRawOpenHiddenIndex source node scope portCount port hroot index)) =
      sourceLocal := by
    funext index
    simp [targetLocal, spawnNodeRawOpenHiddenIndex, hiddenLength]
  change (((extendWireEnv outerEnv targetLocal) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires))) ∘
      (spawnNodeRawOpenRootEmbedding source node scope portCount port
        hroot).index) =
    ((extendWireEnv
      (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port)
      (fun index => targetLocal
        (spawnNodeRawOpenHiddenIndex source node scope portCount port hroot
          index))) ∘
      Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires))) at henv
  rw [hlocal] at henv
  have hrenamed := (denoteItemSeq_renameWires (relCtx := []) model named
    (spawnNodeRawOpenRootEmbedding source node scope portCount port hroot).index
    ((extendWireEnv outerEnv targetLocal) ∘
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    PUnit.unit sourceItems).2 ((congrArg
      (fun current => denoteItemSeq (relCtx := []) model named current
        PUnit.unit sourceItems) henv).mpr hsourceRaw)
  have hfresh : ∀ fresh : Fin portCount,
      ((extendWireEnv outerEnv targetLocal) ∘
        Fin.cast (List.length_append
          (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
          (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
        (spawnNodeRawOpenFreshRootIndex source node scope portCount port hroot
          fresh) = freshValues fresh := by
    intro fresh
    let hiddenFresh : Fin
        (spawnNodeRawOpen source node scope portCount port).hiddenWires.length :=
      Fin.cast hiddenLength.symm
        (Fin.natAdd source.hiddenWires.length fresh)
    let rootFresh : Fin
        (spawnNodeRawOpen source node scope portCount port).rootWires.length :=
      Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)).symm
        (Fin.natAdd
          (spawnNodeRawOpen source node scope portCount port).exposedWires.length
          hiddenFresh)
    have hexposedLength :
        (spawnNodeRawOpen source node scope portCount port).exposedWires.length =
          source.exposedWires.length := by
      rw [spawnNodeRawOpen_exposedWires]
      exact List.length_map _
    have hindex : spawnNodeRawOpenFreshRootIndex source node scope portCount port
        hroot fresh = rootFresh := by
      apply Fin.ext
      simp only [spawnNodeRawOpenFreshRootIndex, rootFresh, hiddenFresh,
        Fin.val_cast, Fin.val_natAdd, OpenConcreteDiagram.rootWires,
        List.length_append]
      rw [hexposedLength]
      omega
    rw [hindex]
    have hrootCast :
        Fin.cast (List.length_append
          (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
          (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires))
          rootFresh =
        Fin.natAdd
          (spawnNodeRawOpen source node scope portCount port).exposedWires.length
          hiddenFresh := by
      apply Fin.ext
      rfl
    change extendWireEnv outerEnv targetLocal
      (Fin.cast (List.length_append
        (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
        (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires))
        rootFresh) = freshValues fresh
    rw [hrootCast]
    simp only [Function.comp_apply, extendWireEnv, Fin.addCases_right]
    have hhiddenCast : Fin.cast hiddenLength hiddenFresh =
        Fin.natAdd source.hiddenWires.length fresh := by
      apply Fin.ext
      rfl
    change Fin.addCases sourceLocal freshValues
      (Fin.cast hiddenLength hiddenFresh) = freshValues fresh
    rw [hhiddenCast]
    exact Fin.addCases_right fresh
  have htargetRaw := hreflect _ hfresh hrenamed
  exact (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (List.length_append
      (as := (spawnNodeRawOpen source node scope portCount port).exposedWires)
      (bs := (spawnNodeRawOpen source node scope portCount port).hiddenWires)))
    (extendWireEnv outerEnv targetLocal) PUnit.unit targetItems).2 htargetRaw

theorem compileOccurrencesWith?_frame_split
    {d : ConcreteDiagram}
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : ConcreteElaboration.WireContext d) →
      ConcreteElaboration.BinderContext d rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext d)
    (binders : ConcreteElaboration.BinderContext d rels)
    (before after : List (ConcreteElaboration.LocalOccurrence
      d.regionCount d.nodeCount))
    (focus : ConcreteElaboration.LocalOccurrence d.regionCount d.nodeCount)
    (items : ItemSeq signature context.length rels)
    (hitems : ConcreteElaboration.compileOccurrencesWith? signature d recurse
      context binders (before ++ focus :: after) = some items) :
    ∃ beforeItems focusItem afterItems,
      ConcreteElaboration.compileOccurrencesWith? signature d recurse context
          binders before = some beforeItems ∧
      ConcreteElaboration.compileOccurrenceWith? signature d recurse context
          binders focus = some focusItem ∧
      ConcreteElaboration.compileOccurrencesWith? signature d recurse context
          binders after = some afterItems ∧
      items = beforeItems.append (.cons focusItem afterItems) := by
  obtain ⟨beforeItems, restItems, hbefore, hrest, hitemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split recurse context
      binders before (focus :: after) items hitems
  simp only [ConcreteElaboration.compileOccurrencesWith?] at hrest
  cases hfocus : ConcreteElaboration.compileOccurrenceWith? signature d recurse
      context binders focus with
  | none => simp [hfocus] at hrest
  | some focusItem =>
      cases hafter : ConcreteElaboration.compileOccurrencesWith? signature d
          recurse context binders after with
      | none => simp [hfocus, hafter] at hrest
      | some afterItems =>
          simp [hfocus, hafter] at hrest
          subst restItems
          exact ⟨beforeItems, focusItem, afterItems, hbefore, rfl, rfl,
            hitemsEq⟩

theorem finishRegion_denote_mono
    (d : ConcreteDiagram) (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (sourceItems targetItems : ItemSeq signature
      (context.extend region).length rels)
    (hitems : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin (context.extend region).length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteItemSeq model named env relEnv sourceItems →
        denoteItemSeq model named env relEnv targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion d context region sourceItems) →
      denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion d context region targetItems) := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  rintro ⟨localEnv, hsource⟩
  refine ⟨localEnv, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at hsource ⊢
  have hsourceRaw := (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
    (extendWireEnv outerEnv localEnv) relEnv sourceItems).1 hsource
  have htargetRaw := hitems model named _ relEnv hsourceRaw
  exact (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
    (extendWireEnv outerEnv localEnv) relEnv targetItems).2 htargetRaw

/-- The reverse semantic obligation at the unique spawn site.  Closed-term
introduction discharges it by choosing the fresh output wire's value to be the
term denotation.  Ordinary polarity-restricted spawning does not need it. -/
def SpawnRegionSiteReflection
    {signature : List Nat}
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) : Prop :=
  ∀ {rels : RelCtx} (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend scope).Exact scope)
    (htargetExact : (target.extend scope).Exact scope)
    (sourceBody : Region signature source.length rels)
    (targetBody : Region signature target.length rels),
    ConcreteElaboration.compileRegion? signature input
        (fuel + 1) scope source binders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port)
          (fuel + 1) scope target binders = some targetBody →
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin target.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody →
          denoteRegion model named outerEnv relEnv targetBody

/-- One compiler induction transports the built-in spawn projection and, when
supplied, the reverse site implication.  Keeping both directions behind this
kernel makes equivalence-capable rules reuse the exact occurrence splitting,
wire renaming, cut reversal, and bubble preservation used by ordinary spawn. -/
private theorem spawnNodeRaw_compileRegion_route_kernel
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (source : ConcreteElaboration.WireContext input)
      (target : ConcreteElaboration.WireContext
        (spawnNodeRaw input node scope portCount port))
      (embedding : SpawnContextEmbedding input node scope portCount port
        source target)
      (binders : ConcreteElaboration.BinderContext input rels)
      (hsourceExact : (source.extend start).Exact start)
      (htargetExact : (target.extend start).Exact start)
      (sourceBody : Region signature source.length rels)
      (targetBody : Region signature target.length rels)
      (hsourceBody : ConcreteElaboration.compileRegion? signature input
        (fuel + 1) start source binders = some sourceBody)
      (htargetBody : ConcreteElaboration.compileRegion? signature
        (spawnNodeRaw input node scope portCount port)
        (fuel + 1) start target binders = some targetBody),
      ((∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin target.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        depth % 2 = 0 →
        denoteRegion model named outerEnv relEnv targetBody →
          denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody) ∧
      (∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin target.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        depth % 2 = 1 →
        denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody →
          denoteRegion model named outerEnv relEnv targetBody)) ∧
      (SpawnRegionSiteReflection (signature := signature) input node scope
          portCount port →
        ( (∀ (model : Lambda.LambdaModel)
            (named : NamedEnv model.Carrier signature)
            (outerEnv : Fin target.length → model.Carrier)
            (relEnv : RelEnv model.Carrier rels),
            depth % 2 = 0 →
            denoteRegion model named (outerEnv ∘ embedding.index) relEnv
                sourceBody →
              denoteRegion model named outerEnv relEnv targetBody) ∧
          (∀ (model : Lambda.LambdaModel)
            (named : NamedEnv model.Carrier signature)
            (outerEnv : Fin target.length → model.Carrier)
            (relEnv : RelEnv model.Carrier rels),
            depth % 2 = 1 →
            denoteRegion model named outerEnv relEnv targetBody →
              denoteRegion model named (outerEnv ∘ embedding.index) relEnv
                sourceBody))) := by
  induction hdepth with
  | here region =>
      intro rels fuel source target embedding binders hsourceExact htargetExact
        sourceBody targetBody hsourceBody htargetBody
      constructor
      · constructor
        · intro model named outerEnv relEnv _ hdenotes
          exact spawnNodeRaw_compileRegion_site_projects input node region
            portCount port hinput htarget hnode fuel source target embedding
            binders hsourceExact htargetExact sourceBody targetBody hsourceBody
            htargetBody model named outerEnv relEnv hdenotes
        · intro _ _ _ _ hodd
          simp at hodd
      · intro hreflect
        constructor
        · intro model named outerEnv relEnv _ hdenotes
          exact hreflect fuel source target embedding binders hsourceExact
            htargetExact sourceBody targetBody hsourceBody htargetBody model
            named outerEnv relEnv hdenotes
        · intro _ _ _ _ hodd
          simp at hodd
  | @cut start child targetRegion rest depth hparent position hposition tail
      child_is_cut tailDepth ih =>
      intro rels fuel source target embedding binders hsourceExact htargetExact
        sourceBody targetBody hsourceBody htargetBody
      have hne : start ≠ targetRegion := by
        intro heq
        subst start
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          hinput hparent) (regionRoute_encloses input hinput tail)
      obtain ⟨before, after, hlocal, hbeforeAway, hafterAway⟩ :=
        localOccurrences_split_at_child input start child position hposition
      simp only [ConcreteElaboration.compileRegion?] at hsourceBody htargetBody
      cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
          input (ConcreteElaboration.compileRegion? signature input fuel)
          (source.extend start) binders
          (ConcreteElaboration.localOccurrences input start) with
      | none => simp [hsourceItems] at hsourceBody
      | some sourceItems =>
        simp [hsourceItems] at hsourceBody
        subst sourceBody
        cases htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node targetRegion portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node targetRegion portCount port) fuel)
            (target.extend start) binders
            (ConcreteElaboration.localOccurrences
              (spawnNodeRaw input node targetRegion portCount port) start) with
        | none => simp [htargetItems] at htargetBody
        | some targetItems =>
          simp [htargetItems] at htargetBody
          subst targetBody
          have htargetLocal :
              ConcreteElaboration.localOccurrences
                  (spawnNodeRaw input node targetRegion portCount port) start =
                (before ++ .child child :: after).map
                  (spawnNodeRaw_oldOccurrence input) := by
            rw [spawnNodeRaw_localOccurrences_old_of_ne input node targetRegion start
              portCount port hnode hne, hlocal]
          have hsourceFramed :
              ConcreteElaboration.compileOccurrencesWith? signature input
                (ConcreteElaboration.compileRegion? signature input fuel)
                (source.extend start) binders
                (before ++ .child child :: after) = some sourceItems := by
            rw [← hlocal]
            exact hsourceItems
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, hsourceBefore,
              hsourceFocus, hsourceAfter, hsourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend start) binders before after (.child child)
              sourceItems hsourceFramed
          have htargetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                (spawnNodeRaw input node targetRegion portCount port)
                (ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input node targetRegion portCount port) fuel)
                (target.extend start) binders
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← htargetLocal]
            exact htargetItems
          obtain ⟨targetBefore, targetFocus, targetAfter, htargetBefore,
              htargetFocus, htargetAfter, htargetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node targetRegion portCount port) fuel)
              (target.extend start) binders
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              htargetFramed
          cases fuel with
          | zero =>
              simp [ConcreteElaboration.compileOccurrenceWith?, child_is_cut,
                ConcreteElaboration.compileRegion?] at hsourceFocus
          | succ childFuel =>
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                spawnNodeRaw_oldOccurrence, child_is_cut] at hsourceFocus htargetFocus
              rw [show (spawnNodeRaw input node targetRegion portCount port).regions
                child = input.regions child by rfl, child_is_cut] at htargetFocus
              cases hsourceChild : ConcreteElaboration.compileRegion? signature
                  input (childFuel + 1) child (source.extend start) binders with
              | none => simp [hsourceChild] at hsourceFocus
              | some sourceChild =>
                simp [hsourceChild] at hsourceFocus
                subst sourceFocus
                cases htargetChild : ConcreteElaboration.compileRegion? signature
                    (spawnNodeRaw input node targetRegion portCount port)
                    (childFuel + 1) child (target.extend start) binders with
                | none =>
                  simp [htargetChild] at htargetFocus
                | some targetChild =>
                  simp [htargetChild] at htargetFocus
                  subst targetFocus
                  have hbeforeMap := spawnNodeRaw_compileOccurrencesAway input
                    node targetRegion start child portCount port hinput htarget
                    hnode hparent tail (childFuel + 1) source target embedding
                    binders hsourceExact htargetExact before (by
                      intro occurrence hmem
                      rw [hlocal]
                      simp [hmem]) hbeforeAway
                  rw [hsourceBefore, htargetBefore] at hbeforeMap
                  have hbeforeEq : targetBefore = sourceBefore.renameWires
                      (embedding.extend start).index :=
                    Option.some.inj hbeforeMap
                  have hafterMap := spawnNodeRaw_compileOccurrencesAway input
                    node targetRegion start child portCount port hinput htarget
                    hnode hparent tail (childFuel + 1) source target embedding
                    binders hsourceExact htargetExact after (by
                      intro occurrence hmem
                      rw [hlocal]
                      simp [hmem]) hafterAway
                  rw [hsourceAfter, htargetAfter] at hafterMap
                  have hafterEq : targetAfter = sourceAfter.renameWires
                      (embedding.extend start).index :=
                    Option.some.inj hafterMap
                  have hchild := ih htarget hnode childFuel
                    (source.extend start) (target.extend start)
                    (embedding.extend start) binders
                    (hsourceExact.extend_child hinput hparent)
                    (htargetExact.extend_child htarget hparent)
                    sourceChild targetChild hsourceChild htargetChild
                  have hfinish := spawnNodeRaw_finishRegion_old_of_ne input node
                    targetRegion start portCount port source target embedding hne
                    sourceItems
                  have hwire : (embedding.extend start).index =
                      spawnNodeRaw_extendedWireMapOfNe embedding start hne := by
                    funext index
                    exact SpawnContextEmbedding.extend_index_eq_map_of_ne
                      embedding start hne htargetExact.nodup index
                  have hfinish' :
                      ConcreteElaboration.finishRegion
                          (spawnNodeRaw input node targetRegion portCount port)
                          target start
                          (sourceItems.renameWires
                            (embedding.extend start).index) =
                        (ConcreteElaboration.finishRegion input source start
                          sourceItems).renameWires embedding.index := by
                    rw [hwire]
                    exact hfinish
                  constructor
                  · constructor
                    · intro model named outerEnv relEnv heven htargetDenotes
                      have htailOdd : depth % 2 = 1 := by omega
                      have hmapped := finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start targetItems
                        (sourceItems.renameWires (embedding.extend start).index)
                        (by
                        intro currentModel currentNamed rawEnv currentRelEnv hitems
                        rw [htargetItemsEq, hbeforeEq, hafterEq,
                          denoteItemSeq_frame] at hitems
                        rw [hsourceItemsEq, ItemSeq.renameWires_append,
                          ItemSeq.renameWires, denoteItemSeq_frame]
                        rcases hitems with ⟨hbefore, hfocus, hafter⟩
                        refine ⟨hbefore, ?_, hafter⟩
                        intro hsourceRenamed
                        have hsourceRaw :=
                          (denoteRegion_renameWires currentModel currentNamed
                            (embedding.extend start).index rawEnv currentRelEnv
                            sourceChild).1 hsourceRenamed
                        exact hfocus (hchild.1.2 currentModel currentNamed rawEnv
                          currentRelEnv htailOdd hsourceRaw))
                        model named outerEnv relEnv htargetDenotes
                      rw [hfinish'] at hmapped
                      exact (denoteRegion_renameWires model named embedding.index
                        outerEnv relEnv
                        (ConcreteElaboration.finishRegion input source start
                          sourceItems)).1 hmapped
                    · intro model named outerEnv relEnv hodd hsourceDenotes
                      have htailEven : depth % 2 = 0 := by omega
                      have hmapped : denoteRegion model named outerEnv relEnv
                          (ConcreteElaboration.finishRegion
                            (spawnNodeRaw input node targetRegion portCount port)
                            target start
                            (sourceItems.renameWires
                              (embedding.extend start).index)) := by
                        rw [hfinish']
                        exact (denoteRegion_renameWires model named embedding.index
                          outerEnv relEnv
                          (ConcreteElaboration.finishRegion input source start
                            sourceItems)).2 hsourceDenotes
                      apply finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start
                        (sourceItems.renameWires (embedding.extend start).index)
                        targetItems _ model named outerEnv relEnv hmapped
                      intro currentModel currentNamed rawEnv currentRelEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hbefore, hfocus, hafter⟩
                      refine ⟨hbefore, ?_, hafter⟩
                      intro htargetRaw
                      have hsourceRaw := hchild.1.1 currentModel currentNamed
                        rawEnv currentRelEnv htailEven htargetRaw
                      exact hfocus ((denoteRegion_renameWires currentModel
                        currentNamed (embedding.extend start).index rawEnv
                        currentRelEnv sourceChild).2 hsourceRaw)
                  · intro hreflect
                    have hchildReverse := hchild.2 hreflect
                    constructor
                    · intro model named outerEnv relEnv heven hsourceDenotes
                      have htailOdd : depth % 2 = 1 := by omega
                      have hmapped : denoteRegion model named outerEnv relEnv
                          (ConcreteElaboration.finishRegion
                            (spawnNodeRaw input node targetRegion portCount port)
                            target start
                            (sourceItems.renameWires
                              (embedding.extend start).index)) := by
                        rw [hfinish']
                        exact (denoteRegion_renameWires model named embedding.index
                          outerEnv relEnv
                          (ConcreteElaboration.finishRegion input source start
                            sourceItems)).2 hsourceDenotes
                      apply finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start
                        (sourceItems.renameWires (embedding.extend start).index)
                        targetItems _ model named outerEnv relEnv hmapped
                      intro currentModel currentNamed rawEnv currentRelEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hbefore, hfocus, hafter⟩
                      refine ⟨hbefore, ?_, hafter⟩
                      intro htargetRaw
                      have hsourceRaw := hchildReverse.2 currentModel currentNamed
                        rawEnv currentRelEnv htailOdd htargetRaw
                      exact hfocus ((denoteRegion_renameWires currentModel
                        currentNamed (embedding.extend start).index rawEnv
                        currentRelEnv sourceChild).2 hsourceRaw)
                    · intro model named outerEnv relEnv hodd htargetDenotes
                      have htailEven : depth % 2 = 0 := by omega
                      have hmapped := finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start targetItems
                        (sourceItems.renameWires (embedding.extend start).index)
                        (by
                        intro currentModel currentNamed rawEnv currentRelEnv hitems
                        rw [htargetItemsEq, hbeforeEq, hafterEq,
                          denoteItemSeq_frame] at hitems
                        rw [hsourceItemsEq, ItemSeq.renameWires_append,
                          ItemSeq.renameWires, denoteItemSeq_frame]
                        rcases hitems with ⟨hbefore, hfocus, hafter⟩
                        refine ⟨hbefore, ?_, hafter⟩
                        intro hsourceRenamed
                        have hsourceRaw :=
                          (denoteRegion_renameWires currentModel currentNamed
                            (embedding.extend start).index rawEnv currentRelEnv
                            sourceChild).1 hsourceRenamed
                        exact hfocus (hchildReverse.1 currentModel currentNamed
                          rawEnv currentRelEnv htailEven hsourceRaw))
                        model named outerEnv relEnv htargetDenotes
                      rw [hfinish'] at hmapped
                      exact (denoteRegion_renameWires model named embedding.index
                        outerEnv relEnv
                        (ConcreteElaboration.finishRegion input source start
                          sourceItems)).1 hmapped
  | @bubble start child targetRegion rest depth arity hparent position hposition
      tail child_is_bubble tailDepth ih =>
      intro rels fuel source target embedding binders hsourceExact htargetExact
        sourceBody targetBody hsourceBody htargetBody
      have hne : start ≠ targetRegion := by
        intro heq
        subst start
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          hinput hparent) (regionRoute_encloses input hinput tail)
      obtain ⟨before, after, hlocal, hbeforeAway, hafterAway⟩ :=
        localOccurrences_split_at_child input start child position hposition
      simp only [ConcreteElaboration.compileRegion?] at hsourceBody htargetBody
      cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
          input (ConcreteElaboration.compileRegion? signature input fuel)
          (source.extend start) binders
          (ConcreteElaboration.localOccurrences input start) with
      | none => simp [hsourceItems] at hsourceBody
      | some sourceItems =>
        simp [hsourceItems] at hsourceBody
        subst sourceBody
        cases htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node targetRegion portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node targetRegion portCount port) fuel)
            (target.extend start) binders
            (ConcreteElaboration.localOccurrences
              (spawnNodeRaw input node targetRegion portCount port) start) with
        | none => simp [htargetItems] at htargetBody
        | some targetItems =>
          simp [htargetItems] at htargetBody
          subst targetBody
          have htargetLocal :
              ConcreteElaboration.localOccurrences
                  (spawnNodeRaw input node targetRegion portCount port) start =
                (before ++ .child child :: after).map
                  (spawnNodeRaw_oldOccurrence input) := by
            rw [spawnNodeRaw_localOccurrences_old_of_ne input node targetRegion
              start portCount port hnode hne, hlocal]
          have hsourceFramed :
              ConcreteElaboration.compileOccurrencesWith? signature input
                (ConcreteElaboration.compileRegion? signature input fuel)
                (source.extend start) binders
                (before ++ .child child :: after) = some sourceItems := by
            rw [← hlocal]
            exact hsourceItems
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, hsourceBefore,
              hsourceFocus, hsourceAfter, hsourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend start) binders before after (.child child)
              sourceItems hsourceFramed
          have htargetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                (spawnNodeRaw input node targetRegion portCount port)
                (ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input node targetRegion portCount port) fuel)
                (target.extend start) binders
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← htargetLocal]
            exact htargetItems
          obtain ⟨targetBefore, targetFocus, targetAfter, htargetBefore,
              htargetFocus, htargetAfter, htargetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node targetRegion portCount port) fuel)
              (target.extend start) binders
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              htargetFramed
          cases fuel with
          | zero =>
              simp [ConcreteElaboration.compileOccurrenceWith?, child_is_bubble,
                ConcreteElaboration.compileRegion?] at hsourceFocus
          | succ childFuel =>
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                spawnNodeRaw_oldOccurrence, child_is_bubble] at hsourceFocus htargetFocus
              rw [show (spawnNodeRaw input node targetRegion portCount port).regions
                child = input.regions child by rfl, child_is_bubble]
                at htargetFocus
              simp only at htargetFocus
              change (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node targetRegion portCount port)
                (childFuel + 1) child (target.extend start)
                (binders.push child arity)).bind
                  (fun body => some (Item.bubble arity body)) =
                    some targetFocus at htargetFocus
              cases hsourceChild : ConcreteElaboration.compileRegion? signature
                  input (childFuel + 1) child (source.extend start)
                  (binders.push child arity) with
              | none => simp [hsourceChild] at hsourceFocus
              | some sourceChild =>
                simp [hsourceChild] at hsourceFocus
                subst sourceFocus
                cases htargetChild : ConcreteElaboration.compileRegion? signature
                    (spawnNodeRaw input node targetRegion portCount port)
                    (childFuel + 1) child (target.extend start)
                    (binders.push child arity) with
                | none =>
                  simp [htargetChild] at htargetFocus
                | some targetChild =>
                  simp [htargetChild] at htargetFocus
                  subst targetFocus
                  have hbeforeMap := spawnNodeRaw_compileOccurrencesAway input
                    node targetRegion start child portCount port hinput htarget
                    hnode hparent tail (childFuel + 1) source target embedding
                    binders hsourceExact htargetExact before (by
                      intro occurrence hmem
                      rw [hlocal]
                      simp [hmem]) hbeforeAway
                  rw [hsourceBefore, htargetBefore] at hbeforeMap
                  have hbeforeEq : targetBefore = sourceBefore.renameWires
                      (embedding.extend start).index :=
                    Option.some.inj hbeforeMap
                  have hafterMap := spawnNodeRaw_compileOccurrencesAway input
                    node targetRegion start child portCount port hinput htarget
                    hnode hparent tail (childFuel + 1) source target embedding
                    binders hsourceExact htargetExact after (by
                      intro occurrence hmem
                      rw [hlocal]
                      simp [hmem]) hafterAway
                  rw [hsourceAfter, htargetAfter] at hafterMap
                  have hafterEq : targetAfter = sourceAfter.renameWires
                      (embedding.extend start).index :=
                    Option.some.inj hafterMap
                  have hchild := ih htarget hnode childFuel
                    (source.extend start) (target.extend start)
                    (embedding.extend start) (binders.push child arity)
                    (hsourceExact.extend_child hinput hparent)
                    (htargetExact.extend_child htarget hparent)
                    sourceChild targetChild hsourceChild htargetChild
                  have hfinish := spawnNodeRaw_finishRegion_old_of_ne input node
                    targetRegion start portCount port source target embedding hne
                    sourceItems
                  have hwire : (embedding.extend start).index =
                      spawnNodeRaw_extendedWireMapOfNe embedding start hne := by
                    funext index
                    exact SpawnContextEmbedding.extend_index_eq_map_of_ne
                      embedding start hne htargetExact.nodup index
                  have hfinish' :
                      ConcreteElaboration.finishRegion
                          (spawnNodeRaw input node targetRegion portCount port)
                          target start
                          (sourceItems.renameWires
                            (embedding.extend start).index) =
                        (ConcreteElaboration.finishRegion input source start
                          sourceItems).renameWires embedding.index := by
                    rw [hwire]
                    exact hfinish
                  constructor
                  · constructor
                    · intro model named outerEnv relEnv heven htargetDenotes
                      have htailEven : depth % 2 = 0 := by omega
                      have hmapped := finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start targetItems
                        (sourceItems.renameWires (embedding.extend start).index)
                        (by
                        intro currentModel currentNamed rawEnv currentRelEnv hitems
                        rw [htargetItemsEq, hbeforeEq, hafterEq,
                          denoteItemSeq_frame] at hitems
                        rw [hsourceItemsEq, ItemSeq.renameWires_append,
                          ItemSeq.renameWires, denoteItemSeq_frame]
                        rcases hitems with ⟨hbefore, hfocus, hafter⟩
                        refine ⟨hbefore, ?_, hafter⟩
                        rcases hfocus with ⟨relation, htargetChildDenotes⟩
                        refine ⟨relation, ?_⟩
                        have hsourceRaw := hchild.1.1 currentModel currentNamed
                          rawEnv (relation, currentRelEnv) htailEven
                          htargetChildDenotes
                        exact (denoteRegion_renameWires
                          (relCtx := arity :: rels) currentModel currentNamed
                          (embedding.extend start).index rawEnv
                          (relation, currentRelEnv) sourceChild).2 hsourceRaw)
                        model named outerEnv relEnv htargetDenotes
                      rw [hfinish'] at hmapped
                      exact (denoteRegion_renameWires model named embedding.index
                        outerEnv relEnv
                        (ConcreteElaboration.finishRegion input source start
                          sourceItems)).1 hmapped
                    · intro model named outerEnv relEnv hodd hsourceDenotes
                      have htailOdd : depth % 2 = 1 := by omega
                      have hmapped : denoteRegion model named outerEnv relEnv
                          (ConcreteElaboration.finishRegion
                            (spawnNodeRaw input node targetRegion portCount port)
                            target start
                            (sourceItems.renameWires
                              (embedding.extend start).index)) := by
                        rw [hfinish']
                        exact (denoteRegion_renameWires model named embedding.index
                          outerEnv relEnv
                          (ConcreteElaboration.finishRegion input source start
                            sourceItems)).2 hsourceDenotes
                      apply finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start
                        (sourceItems.renameWires (embedding.extend start).index)
                        targetItems _ model named outerEnv relEnv hmapped
                      intro currentModel currentNamed rawEnv currentRelEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hbefore, hfocus, hafter⟩
                      refine ⟨hbefore, ?_, hafter⟩
                      rcases hfocus with ⟨relation, hsourceRenamed⟩
                      refine ⟨relation, ?_⟩
                      have hsourceRaw :=
                        (denoteRegion_renameWires (relCtx := arity :: rels)
                          currentModel currentNamed
                          (embedding.extend start).index rawEnv
                          (relation, currentRelEnv) sourceChild).1 hsourceRenamed
                      exact hchild.1.2 currentModel currentNamed rawEnv
                        (relation, currentRelEnv) htailOdd hsourceRaw
                  · intro hreflect
                    have hchildReverse := hchild.2 hreflect
                    constructor
                    · intro model named outerEnv relEnv heven hsourceDenotes
                      have htailEven : depth % 2 = 0 := by omega
                      have hmapped : denoteRegion model named outerEnv relEnv
                          (ConcreteElaboration.finishRegion
                            (spawnNodeRaw input node targetRegion portCount port)
                            target start
                            (sourceItems.renameWires
                              (embedding.extend start).index)) := by
                        rw [hfinish']
                        exact (denoteRegion_renameWires model named embedding.index
                          outerEnv relEnv
                          (ConcreteElaboration.finishRegion input source start
                            sourceItems)).2 hsourceDenotes
                      apply finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start
                        (sourceItems.renameWires (embedding.extend start).index)
                        targetItems _ model named outerEnv relEnv hmapped
                      intro currentModel currentNamed rawEnv currentRelEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hbefore, hfocus, hafter⟩
                      refine ⟨hbefore, ?_, hafter⟩
                      rcases hfocus with ⟨relation, hsourceRenamed⟩
                      refine ⟨relation, ?_⟩
                      have hsourceRaw :=
                        (denoteRegion_renameWires (relCtx := arity :: rels)
                          currentModel currentNamed
                          (embedding.extend start).index rawEnv
                          (relation, currentRelEnv) sourceChild).1 hsourceRenamed
                      exact hchildReverse.1 currentModel currentNamed rawEnv
                        (relation, currentRelEnv) htailEven hsourceRaw
                    · intro model named outerEnv relEnv hodd htargetDenotes
                      have htailOdd : depth % 2 = 1 := by omega
                      have hmapped := finishRegion_denote_mono
                        (spawnNodeRaw input node targetRegion portCount port)
                        target start targetItems
                        (sourceItems.renameWires (embedding.extend start).index)
                        (by
                        intro currentModel currentNamed rawEnv currentRelEnv hitems
                        rw [htargetItemsEq, hbeforeEq, hafterEq,
                          denoteItemSeq_frame] at hitems
                        rw [hsourceItemsEq, ItemSeq.renameWires_append,
                          ItemSeq.renameWires, denoteItemSeq_frame]
                        rcases hitems with ⟨hbefore, hfocus, hafter⟩
                        refine ⟨hbefore, ?_, hafter⟩
                        rcases hfocus with ⟨relation, htargetChildDenotes⟩
                        refine ⟨relation, ?_⟩
                        have hsourceRaw := hchildReverse.2 currentModel
                          currentNamed rawEnv (relation, currentRelEnv) htailOdd
                          htargetChildDenotes
                        exact (denoteRegion_renameWires
                          (relCtx := arity :: rels) currentModel currentNamed
                          (embedding.extend start).index rawEnv
                          (relation, currentRelEnv) sourceChild).2 hsourceRaw)
                        model named outerEnv relEnv htargetDenotes
                      rw [hfinish'] at hmapped
                      exact (denoteRegion_renameWires model named embedding.index
                        outerEnv relEnv
                        (ConcreteElaboration.finishRegion input source start
                          sourceItems)).1 hmapped

/-- Compiler-level spawn projection transported from the spawn site through
each enclosing cut or bubble. -/
theorem spawnNodeRaw_compileRegion_route_projects
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    {rels : RelCtx} (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend start).Exact start)
    (htargetExact : (target.extend start).Exact start)
    (sourceBody : Region signature source.length rels)
    (targetBody : Region signature target.length rels)
    (hsourceBody : ConcreteElaboration.compileRegion? signature input
      (fuel + 1) start source binders = some sourceBody)
    (htargetBody : ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port)
      (fuel + 1) start target binders = some targetBody) :
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin target.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      depth % 2 = 0 →
      denoteRegion model named outerEnv relEnv targetBody →
        denoteRegion model named (outerEnv ∘ embedding.index) relEnv
          sourceBody) ∧
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin target.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      depth % 2 = 1 →
      denoteRegion model named (outerEnv ∘ embedding.index) relEnv
          sourceBody →
        denoteRegion model named outerEnv relEnv targetBody) :=
  (spawnNodeRaw_compileRegion_route_kernel input node scope portCount port
    hinput htarget hnode route hdepth fuel source target embedding binders
    hsourceExact htargetExact sourceBody targetBody hsourceBody htargetBody).1

/-- A reverse spawn-site proof is transported by the same compiler induction
as the ordinary projection.  At even cut depth it introduces the spawned
body; at odd depth it reflects it through the enclosing negation. -/
theorem spawnNodeRaw_compileRegion_route_reflects
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (hreflect : SpawnRegionSiteReflection (signature := signature) input node
      scope portCount port)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    {rels : RelCtx} (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend start).Exact start)
    (htargetExact : (target.extend start).Exact start)
    (sourceBody : Region signature source.length rels)
    (targetBody : Region signature target.length rels)
    (hsourceBody : ConcreteElaboration.compileRegion? signature input
      (fuel + 1) start source binders = some sourceBody)
    (htargetBody : ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port)
      (fuel + 1) start target binders = some targetBody) :
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin target.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      depth % 2 = 0 →
      denoteRegion model named (outerEnv ∘ embedding.index) relEnv
          sourceBody →
        denoteRegion model named outerEnv relEnv targetBody) ∧
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin target.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      depth % 2 = 1 →
      denoteRegion model named outerEnv relEnv targetBody →
        denoteRegion model named (outerEnv ∘ embedding.index) relEnv
          sourceBody) :=
  (spawnNodeRaw_compileRegion_route_kernel input node scope portCount port
    hinput htarget hnode route hdepth fuel source target embedding binders
    hsourceExact htargetExact sourceBody targetBody hsourceBody htargetBody).2
      hreflect

theorem regionRoute_hasCutDepth_exists
    (hinput : input.WellFormed signature)
    (route : Diagram.Splice.RegionRoute input start target path) :
    ∃ depth, route.HasCutDepth depth := by
  induction route with
  | here => exact ⟨0, .here _⟩
  | @step start child target rest hparent position hposition tail ih =>
      obtain ⟨depth, hdepth⟩ := ih
      cases hregion : input.regions child with
      | sheet => simp [hregion, CRegion.parent?] at hparent
      | cut parent =>
          have : parent = start := by
            simpa [hregion, CRegion.parent?] using hparent
          subst parent
          exact ⟨depth + 1,
            Diagram.Splice.RegionRoute.HasCutDepth.cut
              (hparent := hparent) (hposition := hposition) hregion hdepth⟩
      | bubble parent arity =>
          have : parent = start := by
            simpa [hregion, CRegion.parent?] using hparent
          subst parent
          exact ⟨depth,
            Diagram.Splice.RegionRoute.HasCutDepth.bubble
              (hparent := hparent) (hposition := hposition) hregion hdepth⟩

private def routeCutDepthAux (diagram : ConcreteDiagram) :
    Nat → Fin diagram.regionCount → Nat
  | 0, _ => 0
  | fuel + 1, region =>
      match diagram.regions region with
      | .sheet => 0
      | .cut parent => routeCutDepthAux diagram fuel parent + 1
      | .bubble parent _ => routeCutDepthAux diagram fuel parent

private theorem routeCutDepthAux_hdepth
    {input : ConcreteDiagram} {start target : Fin input.regionCount}
    {path : List Nat}
    {route : Diagram.Splice.RegionRoute input start target path}
    (hdepth : Diagram.Splice.RegionRoute.HasCutDepth route depth) (fuel : Nat) :
    routeCutDepthAux input (path.length + fuel) target =
      routeCutDepthAux input fuel start + depth := by
  induction hdepth generalizing fuel with
  | here => simp [routeCutDepthAux]
  | @cut start child target rest depth hparent position hposition tail
      child_is_cut tail_depth ih =>
      rw [show (position.val :: rest).length + fuel =
        rest.length + (fuel + 1) by simp; omega]
      rw [ih (fuel + 1)]
      simp [routeCutDepthAux, child_is_cut]
      omega
  | @bubble start child target rest depth arity hparent position hposition tail
      child_is_bubble tail_depth ih =>
      rw [show (position.val :: rest).length + fuel =
        rest.length + (fuel + 1) by simp; omega]
      rw [ih (fuel + 1)]
      simp [routeCutDepthAux, child_is_bubble]

theorem regionRoute_cutDepth_unique
    {input : ConcreteDiagram} {start target : Fin input.regionCount}
    {path : List Nat}
    {route : Diagram.Splice.RegionRoute input start target path}
    (left : Diagram.Splice.RegionRoute.HasCutDepth route leftDepth)
    (right : Diagram.Splice.RegionRoute.HasCutDepth route rightDepth) :
    leftDepth = rightDepth := by
  have hleft := routeCutDepthAux_hdepth left 0
  have hright := routeCutDepthAux_hdepth right 0
  simp only [Nat.add_zero, routeCutDepthAux, Nat.zero_add] at hleft hright
  omega

end VisualProof.Rule
