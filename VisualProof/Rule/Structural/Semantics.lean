import VisualProof.Rule.Structural.Iteration
import VisualProof.Diagram.ContextReachability
import VisualProof.Rule.Laws

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

/-- Intrinsic contraction for the splice kernel.  If the unchanged host
items already force the inserted material at the exact wire and lexical
relation assignment selected by the splice, adjoining that material is an
equivalence.  Iteration's concrete proof is responsible only for supplying
`available` from its retained ancestor occurrence. -/
theorem spliceAt_contraction_sound
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outerWires + hostLocal) hostRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (outerWires + hostLocal))
    (relationMap : RelationRenaming materialRels hostRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier hostRels)
    (available : ∀ hostEnv : Fin hostLocal → model.Carrier,
      denoteItemSeq model  (extendWireEnv env hostEnv) rels hostItems →
        denoteRegion model
          (extendWireEnv env hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap rels) material) :
    denoteRegion model  env rels
        (Region.spliceAt hostLocal hostItems material wireMap relationMap) ↔
      denoteRegion model  env rels (.mk hostLocal hostItems) := by
  rw [Region.denote_spliceAt model  env rels
      (RelEnv.pullback relationMap rels) hostLocal hostItems material wireMap
      relationMap (RelEnv.pullback_agrees relationMap rels)]
  change
    (∃ hostEnv : Fin hostLocal → model.Carrier,
      denoteItemSeq model  (extendWireEnv env hostEnv) rels hostItems ∧
        denoteRegion model  (extendWireEnv env hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap rels) material) ↔
      ∃ hostEnv : Fin hostLocal → model.Carrier,
        denoteItemSeq model  (extendWireEnv env hostEnv) rels hostItems
  constructor
  · rintro ⟨hostEnv, hhost, _⟩
    exact ⟨hostEnv, hhost⟩
  · rintro ⟨hostEnv, hhost⟩
    exact ⟨hostEnv, hhost, available hostEnv hhost⟩

/-- Ancestor contraction at an actual splice site.  The copied material may
use both descendant-visible wires and the target region's local witnesses.
The retained ancestor occurrence supplies it for precisely the descendant
valuations reachable through the retained context. -/
theorem ancestorSpliceCopy_sound
    (outer : DiagramContext  outerWires ancestorWires outerRels
      ancestorRels)
    (descendant : DiagramContext  ancestorWires descendantWires
      ancestorRels descendantRels)
    (ancestor : Region  ancestorWires ancestorRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (descendantWires + hostLocal)
      descendantRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (descendantWires + hostLocal))
    (relationMap : RelationRenaming materialRels descendantRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (copyTransport : ∀
      (ancestorEnv : Fin ancestorWires → model.Carrier)
      (ancestorRelEnv : RelEnv model.Carrier ancestorRels),
      denoteRegion model  ancestorEnv ancestorRelEnv ancestor →
        ∀ (descendantEnv : Fin descendantWires → model.Carrier)
          (descendantRelEnv : RelEnv model.Carrier descendantRels)
          (_reachable : descendant.Reachable ancestorEnv ancestorRelEnv
            descendantEnv descendantRelEnv)
          (hostEnv : Fin hostLocal → model.Carrier),
          denoteItemSeq model
              (extendWireEnv descendantEnv hostEnv) descendantRelEnv hostItems →
            denoteRegion model
              (extendWireEnv descendantEnv hostEnv ∘ wireMap)
              (RelEnv.pullback relationMap descendantRelEnv) material) :
    denoteRegion model  env rels
        (outer.fill
          (ancestor.conjoin
            (descendant.fill (.mk hostLocal hostItems)))) ↔
      denoteRegion model  env rels
        (outer.fill
          (ancestor.conjoin
            (descendant.fill
              (Region.spliceAt hostLocal hostItems material wireMap
                relationMap)))) := by
  apply outer.fill_equiv
  intro ancestorEnv ancestorRelEnv
  rw [Region.denote_conjoin, Region.denote_conjoin]
  constructor
  · rintro ⟨ancestorDenotes, hostDenotes⟩
    refine ⟨ancestorDenotes, ?_⟩
    apply (descendant.fill_equiv_of_reachable (.mk hostLocal hostItems)
      (Region.spliceAt hostLocal hostItems material wireMap relationMap)
      model  ancestorEnv ancestorRelEnv
      (fun descendantEnv descendantRelEnv reachable =>
        (spliceAt_contraction_sound hostLocal hostItems material wireMap
          relationMap model  descendantEnv descendantRelEnv
          (copyTransport ancestorEnv ancestorRelEnv ancestorDenotes
            descendantEnv descendantRelEnv reachable)).symm)).mp
    exact hostDenotes
  · rintro ⟨ancestorDenotes, copiedDenotes⟩
    refine ⟨ancestorDenotes, ?_⟩
    apply (descendant.fill_equiv_of_reachable (.mk hostLocal hostItems)
      (Region.spliceAt hostLocal hostItems material wireMap relationMap)
      model  ancestorEnv ancestorRelEnv
      (fun descendantEnv descendantRelEnv reachable =>
        (spliceAt_contraction_sound hostLocal hostItems material wireMap
          relationMap model  descendantEnv descendantRelEnv
          (copyTransport ancestorEnv ancestorRelEnv ancestorDenotes
            descendantEnv descendantRelEnv reachable)).symm)).mpr
    exact copiedDenotes

/-- `spliceAt_contraction_sound` remains valid after the outer-wire and
lexical-relation transports used by the concrete splice compiler. -/
theorem spliceAt_contraction_renamed_sound
    (hostLocal : Nat)
    (hostItems : ItemSeq  (outerWires + hostLocal) hostRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (outerWires + hostLocal))
    (relationMap : RelationRenaming materialRels hostRels)
    (outerMap : Fin outerWires → Fin targetWires)
    (hostRelationMap : RelationRenaming hostRels targetRels)
    (model : Model)
    (env : Fin targetWires → model.Carrier)
    (rels : RelEnv model.Carrier targetRels)
    (available : ∀ hostEnv : Fin hostLocal → model.Carrier,
      denoteItemSeq model
          (extendWireEnv (env ∘ outerMap) hostEnv)
          (RelEnv.pullback hostRelationMap rels) hostItems →
        denoteRegion model
          (extendWireEnv (env ∘ outerMap) hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap
            (RelEnv.pullback hostRelationMap rels)) material) :
    denoteRegion model  env rels
        (((Region.spliceAt hostLocal hostItems material wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) ↔
      denoteRegion model  env rels
        (((Region.mk hostLocal hostItems).renameRelations hostRelationMap)
          |>.renameWires outerMap) := by
  rw [denoteRegion_renameWires, denoteRegion_renameWires,
    denoteRegion_renameRelations model  hostRelationMap
      (RelEnv.pullback hostRelationMap rels) rels
      (RelEnv.pullback_agrees hostRelationMap rels) (env ∘ outerMap),
    denoteRegion_renameRelations model  hostRelationMap
      (RelEnv.pullback hostRelationMap rels) rels
      (RelEnv.pullback_agrees hostRelationMap rels) (env ∘ outerMap)]
  exact spliceAt_contraction_sound hostLocal hostItems material wireMap
    relationMap model  (env ∘ outerMap)
    (RelEnv.pullback hostRelationMap rels) available

/-- Contextual form of splice contraction.  Because the local law is an
equivalence, no cut-polarity premise is needed. -/
theorem fill_spliceAt_contraction_sound
    (ctx : DiagramContext  outerWires holeWires outerRels holeRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq  (holeWires + hostLocal) holeRels)
    (material : Region  materialWires materialRels)
    (wireMap : Fin materialWires → Fin (holeWires + hostLocal))
    (relationMap : RelationRenaming materialRels holeRels)
    (model : Model)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (available : ∀
      (holeEnv : Fin holeWires → model.Carrier)
      (holeRelEnv : RelEnv model.Carrier holeRels)
      (hostEnv : Fin hostLocal → model.Carrier),
      denoteItemSeq model  (extendWireEnv holeEnv hostEnv) holeRelEnv
          hostItems →
        denoteRegion model
          (extendWireEnv holeEnv hostEnv ∘ wireMap)
          (RelEnv.pullback relationMap holeRelEnv) material) :
    denoteRegion model  env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems material wireMap relationMap)) ↔
      denoteRegion model  env rels
        (ctx.fill (.mk hostLocal hostItems)) := by
  apply ctx.fill_equiv
  intro holeEnv holeRelEnv
  exact spliceAt_contraction_sound hostLocal hostItems material wireMap
    relationMap model  holeEnv holeRelEnv
    (available holeEnv holeRelEnv)

end VisualProof.Rule
