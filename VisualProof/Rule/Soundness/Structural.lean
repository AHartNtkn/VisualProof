import VisualProof.Concrete.Elaboration.Simulation
import VisualProof.Rule.Soundness
import VisualProof.Rule.Soundness.Modal.EliminationRootSimulation
import VisualProof.Rule.Soundness.Modal.VacuousEliminationRootSimulation
import VisualProof.Rule.Soundness.Modal.VacuousRoot
import VisualProof.Rule.Soundness.Iteration.OpenRoute
import VisualProof.Rule.Soundness.Iteration.ZeroOpenRoute
import VisualProof.Rule.Soundness.Iteration.RootAnchorSemantic
import VisualProof.Rule.Soundness.Iteration.SameSite
import VisualProof.Rule.Soundness.Iteration.DeiterationSemantic
import VisualProof.Rule.Soundness.WireJoin

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

private theorem allFin_succ_last_soundness (n : Nat) :
    allFin (n + 1) =
      (allFin n).map Fin.castSucc ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]

private theorem eraseDups_map_injective_soundness
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinjective : Function.Injective f) :
    ∀ values : List α,
      (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← eraseDups_map_injective_soundness f hinjective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp [hinjective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem listGet_cast_of_eq {left right : List α}
    (equality : left = right) (index : Fin left.length) :
    left.get index = right.get (Fin.cast (congrArg List.length equality) index) := by
  subst right
  rfl

private theorem listGet_map_cast_soundness (values : List α) (f : α → β)
    (index : Fin values.length) :
    (values.map f).get
        (Fin.cast (List.length_map (as := values) f).symm index) =
      f (values.get index) := by
  simpa only [List.get_eq_getElem, Fin.val_cast] using
    (List.getElem_map (l := values) (i := index.val) f)

/-!
Boundary-parametric soundness for the structural receipt family.

Every operation below is normalized through `OperationReceipt.Realizes`; the
operation-specific part of each proof therefore reasons about the exact raw
graph returned by the executor, while the generic receipt theorem owns the
final checked-result and ordered-boundary casts.
-/

private def realizedOperationalOpen
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {provenance : WireProvenance input.val raw}
    {interface : WireTransport input.val raw}
    (realizes : receipt.Realizes raw provenance interface)
    {boundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.CheckedOpen  :=
  ⟨realizes.rawResultOpen mapped,
    realizes.rawResultOpen_wellFormed sourceRoot htransport⟩

private def realizedOperationalIso
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {provenance : WireProvenance input.val raw}
    {interface : WireTransport input.val raw}
    (realizes : receipt.Realizes raw provenance interface)
    {boundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.OpenIso
      (realizedOperationalOpen realizes sourceRoot htransport).val
      (realizes.rawResultOpen mapped) :=
  Concrete.OpenIso.refl _

@[simp] private theorem severWireRaw_regionCount
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).regionCount = input.regionCount :=
  rfl

@[simp] private theorem severWireRaw_nodeCount
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).nodeCount = input.nodeCount :=
  rfl

@[simp] private theorem severWireRaw_root
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).root = input.root :=
  rfl

@[simp] private theorem severWireRaw_regions
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount) :
    (severWireRaw input wire keep).regions region = input.regions region :=
  rfl

@[simp] private theorem severWireRaw_nodes
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (node : Fin input.nodeCount) :
    (severWireRaw input wire keep).nodes node = input.nodes node :=
  rfl

@[simp] private theorem severWireRaw_oldWire
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).wires candidate.castSucc =
      if candidate = wire then
        { scope := (input.wires wire).scope
          endpoints := (input.wires wire).endpoints.filter
            (fun endpoint => decide (endpoint ∈ keep)) }
      else input.wires candidate := by
  simp [severWireRaw]

@[simp] private theorem severWireRaw_freshWire
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).wires (Fin.last input.wireCount) =
      { scope := (input.wires wire).scope
        endpoints := (input.wires wire).endpoints.filter
          (fun endpoint => decide (endpoint ∉ keep)) } := by
  simp [severWireRaw]

private theorem severWireRaw_oldWire_scope
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    ((severWireRaw input wire keep).wires candidate.castSucc).scope =
      (input.wires candidate).scope := by
  by_cases hcandidate : candidate = wire
  · subst candidate
    simp
  · simp [hcandidate]

private theorem severWireRaw_freshWire_scope
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    ((severWireRaw input wire keep).wires
      (Fin.last input.wireCount)).scope = (input.wires wire).scope := by
  simp

private theorem severWireRaw_exactScopeWires
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount) :
    Concrete.Elaboration.exactScopeWires (severWireRaw input wire keep) region =
      (Concrete.Elaboration.exactScopeWires input region).map Fin.castSucc ++
        if region = (input.wires wire).scope then
          [Fin.last input.wireCount]
        else [] := by
  unfold Concrete.Elaboration.exactScopeWires filterFin
  change List.filter _ (allFin (input.wireCount + 1)) = _
  rw [allFin_succ_last_soundness, List.filter_append]
  simp only [List.filter_map]
  congr 1
  · apply congrArg (List.map Fin.castSucc)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.wireCount))
    funext candidate
    simp only [Function.comp_apply]
    rw [severWireRaw_oldWire_scope]
    rfl
  · simp only [List.filter_cons, List.filter_nil]
    by_cases hscope : region = (input.wires wire).scope
    · rw [if_pos hscope]
      have hdecide : decide
          (((severWireRaw input wire keep).wires
            (Fin.last input.wireCount)).scope = region) = true := by
        apply decide_eq_true
        rw [severWireRaw_freshWire_scope, hscope]
      rw [hdecide]
      rfl

    · rw [if_neg hscope]
      have hdecide : decide
          (((severWireRaw input wire keep).wires
            (Fin.last input.wireCount)).scope = region) = false := by
        apply decide_eq_false
        rw [severWireRaw_freshWire_scope]
        exact fun equality => hscope equality.symm
      rw [hdecide]
      rfl

private theorem severWireRaw_exactScopeWires_of_ne
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope) :
    Concrete.Elaboration.exactScopeWires (severWireRaw input wire keep) region =
      (Concrete.Elaboration.exactScopeWires input region).map Fin.castSucc := by
  rw [severWireRaw_exactScopeWires]
  simp [hne]

private theorem severWireRaw_exactScopeWires_length_of_ne
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope) :
    (Concrete.Elaboration.exactScopeWires
      (severWireRaw input wire keep) region).length =
      (Concrete.Elaboration.exactScopeWires input region).length := by
  rw [severWireRaw_exactScopeWires_of_ne input wire keep region hne]
  exact List.length_map _

private theorem severWireRaw_oldEndpointOccurs_iff
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (endpoint : CEndpoint input.nodeCount) :
    (severWireRaw input wire keep).EndpointOccurs candidate.castSucc endpoint ↔
      input.EndpointOccurs candidate endpoint ∧
        (candidate = wire → endpoint ∈ keep) := by
  unfold Concrete.Diagram.EndpointOccurs
  by_cases hcandidate : candidate = wire
  · subst candidate
    rw [severWireRaw_oldWire, if_pos rfl]
    change endpoint ∈
        (input.wires wire).endpoints.filter
          (fun candidate => decide (candidate ∈ keep)) ↔
      input.EndpointOccurs wire endpoint ∧
        (wire = wire → endpoint ∈ keep)
    rw [List.mem_filter]
    constructor
    · rintro ⟨hoccurs, hkeep⟩
      exact ⟨hoccurs, fun _ => of_decide_eq_true hkeep⟩
    · rintro ⟨hoccurs, hkeep⟩
      exact ⟨hoccurs, decide_eq_true (hkeep rfl)⟩
  · rw [severWireRaw_oldWire, if_neg hcandidate]
    constructor
    · intro hoccurs
      exact ⟨hoccurs, fun equality => False.elim (hcandidate equality)⟩
    · exact And.left

private theorem severWireRaw_freshEndpointOccurs_iff
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (endpoint : CEndpoint input.nodeCount) :
    (severWireRaw input wire keep).EndpointOccurs
        (Fin.last input.wireCount) endpoint ↔
      input.EndpointOccurs wire endpoint ∧ endpoint ∉ keep := by
  unfold Concrete.Diagram.EndpointOccurs
  rw [severWireRaw_freshWire, List.mem_filter]
  constructor
  · rintro ⟨hoccurs, hnotKeep⟩
    exact ⟨hoccurs, of_decide_eq_true hnotKeep⟩
  · rintro ⟨hoccurs, hnotKeep⟩
    exact ⟨hoccurs, decide_eq_true hnotKeep⟩

private theorem severWireRaw_endpointOccurs_forward
    (input : Concrete.Diagram) (wire source : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (endpoint : CEndpoint input.nodeCount)
    (occurs : input.EndpointOccurs source endpoint) :
    (source = wire ∧ endpoint ∉ keep ∧
        (severWireRaw input wire keep).EndpointOccurs
          (Fin.last input.wireCount) endpoint) ∨
      (severWireRaw input wire keep).EndpointOccurs source.castSucc endpoint := by
  by_cases hsource : source = wire
  · by_cases hkeep : endpoint ∈ keep
    · exact Or.inr ((severWireRaw_oldEndpointOccurs_iff input wire source keep
        endpoint).2 ⟨occurs, fun _ => hkeep⟩)
    · exact Or.inl ⟨hsource, hkeep,
        (severWireRaw_freshEndpointOccurs_iff input wire keep endpoint).2
          ⟨hsource ▸ occurs, hkeep⟩⟩
  · exact Or.inr ((severWireRaw_oldEndpointOccurs_iff input wire source keep
      endpoint).2 ⟨occurs, fun equality => (hsource equality).elim⟩)

private def severWireCollapse (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    Fin (severWireRaw input wire keep).wireCount → Fin input.wireCount :=
  Fin.lastCases wire id

@[simp] private theorem severWireCollapse_old
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    severWireCollapse input wire keep candidate.castSucc =
      candidate := by
  simp [severWireCollapse]

@[simp] private theorem severWireCollapse_fresh
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    severWireCollapse input wire keep (Fin.last input.wireCount) =
      wire := by
  simp [severWireCollapse]

private theorem severWireRaw_endpointOccurs_collapse
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (candidate : Fin (severWireRaw input wire keep).wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (occurs : (severWireRaw input wire keep).EndpointOccurs
      candidate endpoint) :
    input.EndpointOccurs
      (severWireCollapse input wire keep candidate) endpoint := by
  refine Fin.lastCases
    (motive := fun current =>
      (severWireRaw input wire keep).EndpointOccurs current endpoint →
        input.EndpointOccurs
          (severWireCollapse input wire keep current) endpoint)
    (fun freshOccurs => by
      simpa [severWireCollapse] using
        ((severWireRaw_freshEndpointOccurs_iff input wire keep endpoint).1
          freshOccurs).1)
    (fun old oldOccurs => by
      simpa [severWireCollapse] using
        ((severWireRaw_oldEndpointOccurs_iff input wire old keep endpoint).1
          oldOccurs).1)
    candidate occurs

private theorem severWireRaw_endpointOccurs_lift
    (input : Concrete.Diagram) (wire source : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (endpoint : CEndpoint input.nodeCount)
    (occurs : input.EndpointOccurs source endpoint) :
    ∃ candidate : Fin (severWireRaw input wire keep).wireCount,
      severWireCollapse input wire keep candidate = source ∧
        (severWireRaw input wire keep).EndpointOccurs candidate endpoint := by
  rcases severWireRaw_endpointOccurs_forward input wire source keep endpoint
    occurs with ⟨hsource, hnotKeep, hfresh⟩ | hold
  · subst source
    exact ⟨Fin.last input.wireCount, by simp, hfresh⟩
  · exact ⟨source.castSucc, by simp, hold⟩

private structure SeverContextCollapse
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (expanded : Concrete.Elaboration.WireContext
      (severWireRaw input wire keep))
    (original : Concrete.Elaboration.WireContext input) where
  indexMap : Fin expanded.length → Fin original.length
  get : ∀ index,
    original.get (indexMap index) =
      severWireCollapse input wire keep (expanded.get index)
  mem : ∀ candidate,
    severWireCollapse input wire keep candidate ∈ original ↔
      candidate ∈ expanded

namespace SeverContextCollapse

private noncomputable def ofMem
    {input : Concrete.Diagram} {wire : Fin input.wireCount}
    {keep : List (CEndpoint input.nodeCount)}
    {expanded : Concrete.Elaboration.WireContext
      (severWireRaw input wire keep)}
    {original : Concrete.Elaboration.WireContext input}
    (hmem : ∀ candidate,
      severWireCollapse input wire keep candidate ∈ original ↔
        candidate ∈ expanded) :
    SeverContextCollapse input wire keep expanded original where
  indexMap := fun index => Classical.choose
    (Concrete.Elaboration.WireContext.lookup?_complete
      ((hmem (expanded.get index)).2 (List.get_mem expanded index)))
  get := by
    intro index
    exact Concrete.Elaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (Concrete.Elaboration.WireContext.lookup?_complete
          ((hmem (expanded.get index)).2
            (List.get_mem expanded index))))
  mem := hmem

end SeverContextCollapse

private theorem severWireRaw_scope_collapse
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (candidate : Fin (severWireRaw input wire keep).wireCount) :
    ((severWireRaw input wire keep).wires candidate).scope =
      (input.wires (severWireCollapse input wire keep candidate)).scope := by
  refine Fin.lastCases
    (motive := fun current =>
      ((severWireRaw input wire keep).wires current).scope =
        (input.wires (severWireCollapse input wire keep current)).scope)
    (by simp [severWireCollapse])
    (fun old => by
      change ((severWireRaw input wire keep).wires old.castSucc).scope =
        (input.wires (severWireCollapse input wire keep old.castSucc)).scope
      rw [severWireCollapse_old]
      exact severWireRaw_oldWire_scope input wire old keep)
    candidate

private theorem severWireRaw_exactScopeWires_mem_collapse
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount)
    (candidate : Fin (severWireRaw input wire keep).wireCount) :
    severWireCollapse input wire keep candidate ∈
        Concrete.Elaboration.exactScopeWires input region ↔
      candidate ∈ Concrete.Elaboration.exactScopeWires
        (severWireRaw input wire keep) region := by
  rw [Concrete.Elaboration.mem_exactScopeWires,
    Concrete.Elaboration.mem_exactScopeWires,
    severWireRaw_scope_collapse]
  rfl

private noncomputable def SeverContextCollapse.extend
    (collapse : SeverContextCollapse input wire keep expanded original)
    (region : Fin input.regionCount) :
    SeverContextCollapse input wire keep
      (expanded.extend region) (original.extend region) :=
  .ofMem (by
    intro candidate
    unfold Concrete.Elaboration.WireContext.extend
    constructor
    · intro hmember
      rcases List.mem_append.mp hmember with hinherited | hlocal
      · exact List.mem_append_left _
          ((collapse.mem candidate).1 hinherited)
      · exact List.mem_append_right _
          ((severWireRaw_exactScopeWires_mem_collapse input wire keep region
            candidate).1 hlocal)
    · intro hmember
      rcases List.mem_append.mp hmember with hinherited | hlocal
      · exact List.mem_append_left _
          ((collapse.mem candidate).2 hinherited)
      · exact List.mem_append_right _
          ((severWireRaw_exactScopeWires_mem_collapse input wire keep region
            candidate).2 hlocal))

private theorem SeverContextCollapse.extend_index_inherited
    (collapse : SeverContextCollapse input wire keep expanded original)
    (region : Fin input.regionCount)
    (originalExtendedNodup : (original.extend region).Nodup)
    (index : Fin expanded.length) :
    (collapse.extend region).indexMap
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend expanded region).symm
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires
              (severWireRaw input wire keep) region).length index)) =
      Fin.cast
        (Concrete.Elaboration.WireContext.length_extend original region).symm
        (Fin.castAdd
          (Concrete.Elaboration.exactScopeWires input region).length
          (collapse.indexMap index)) := by
  let expandedIndex : Fin (expanded.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend expanded region).symm
      (Fin.castAdd
        (Concrete.Elaboration.exactScopeWires
          (severWireRaw input wire keep) region).length index)
  let originalIndex : Fin (original.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend original region).symm
      (Fin.castAdd
        (Concrete.Elaboration.exactScopeWires input region).length
        (collapse.indexMap index))
  change (collapse.extend region).indexMap expandedIndex = originalIndex
  have hexpandedGet :
      (expanded.extend region).get expandedIndex = expanded.get index := by
    simp [expandedIndex, Concrete.Elaboration.WireContext.extend]
  have horiginalGet :
      (original.extend region).get originalIndex =
        original.get (collapse.indexMap index) := by
    simp [originalIndex, Concrete.Elaboration.WireContext.extend]
  have hleft := (collapse.extend region).get expandedIndex
  rw [hexpandedGet] at hleft
  have hget :
      (original.extend region).get
          ((collapse.extend region).indexMap expandedIndex) =
        (original.extend region).get originalIndex :=
    hleft.trans ((collapse.get index).symm.trans horiginalGet.symm)
  apply Fin.ext
  exact (List.getElem_inj originalExtendedNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

private theorem SeverContextCollapse.extend_index_local_of_ne
    (collapse : SeverContextCollapse input wire keep expanded original)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope)
    (originalExtendedNodup : (original.extend region).Nodup)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      (severWireRaw input wire keep) region).length) :
    (collapse.extend region).indexMap
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length index)) =
      Fin.cast
        (Concrete.Elaboration.WireContext.length_extend original region).symm
        (Fin.natAdd original.length
          (Fin.cast
            (severWireRaw_exactScopeWires_length_of_ne input wire keep region
              hne)
            index)) := by
  let expandedIndex : Fin (expanded.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend expanded region).symm
      (Fin.natAdd expanded.length index)
  let sourceLocal := Fin.cast
    (severWireRaw_exactScopeWires_length_of_ne input wire keep region hne)
    index
  let originalIndex : Fin (original.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend original region).symm
      (Fin.natAdd original.length sourceLocal)
  change (collapse.extend region).indexMap expandedIndex = originalIndex
  have hexpandedGet :
      (expanded.extend region).get expandedIndex =
        (Concrete.Elaboration.exactScopeWires
          (severWireRaw input wire keep) region).get index := by
    simp [expandedIndex, Concrete.Elaboration.WireContext.extend]
  have htargetLocal :
      (Concrete.Elaboration.exactScopeWires
          (severWireRaw input wire keep) region).get index =
        Fin.castSucc
          ((Concrete.Elaboration.exactScopeWires input region).get sourceLocal) := by
    have hlist := severWireRaw_exactScopeWires_of_ne input wire keep region hne
    have hget := listGet_cast_of_eq hlist index
    have hindex :
        Fin.cast
            (List.length_map
              (as := Concrete.Elaboration.exactScopeWires input region)
              Fin.castSucc).symm sourceLocal =
          Fin.cast (congrArg List.length hlist) index := by
      apply Fin.ext
      rfl
    rw [← hindex] at hget
    exact hget.trans
      (listGet_map_cast_soundness
        (Concrete.Elaboration.exactScopeWires input region) Fin.castSucc
        sourceLocal)
  have horiginalGet :
      (original.extend region).get originalIndex =
        (Concrete.Elaboration.exactScopeWires input region).get sourceLocal := by
    simp [originalIndex, Concrete.Elaboration.WireContext.extend]
  have hleft := (collapse.extend region).get expandedIndex
  rw [hexpandedGet, htargetLocal, severWireCollapse_old] at hleft
  have hget :
      (original.extend region).get
          ((collapse.extend region).indexMap expandedIndex) =
        (original.extend region).get originalIndex :=
    hleft.trans horiginalGet.symm
  apply Fin.ext
  exact (List.getElem_inj originalExtendedNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

private def severExtendedEnv
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (Concrete.Elaboration.exactScopeWires input region).length → D) :
    Fin (context.extend region).length → D :=
  extendWireEnv outerEnv localEnv ∘
    Fin.cast (Concrete.Elaboration.WireContext.length_extend context region)

private noncomputable def severTargetLocalEnv
    (collapse : SeverContextCollapse input wire keep expanded original)
    (region : Fin input.regionCount)
    (sourceOuter : Fin original.length → D)
    (sourceLocal :
      Fin (Concrete.Elaboration.exactScopeWires input region).length → D) :
    Fin (Concrete.Elaboration.exactScopeWires
      (severWireRaw input wire keep) region).length → D :=
  fun localIndex =>
    severExtendedEnv original region sourceOuter sourceLocal
      ((collapse.extend region).indexMap
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length localIndex)))

private theorem severExtendedEnv_collapse
    (collapse : SeverContextCollapse input wire keep expanded original)
    (region : Fin input.regionCount)
    (originalExtendedNodup : (original.extend region).Nodup)
    (sourceOuter : Fin original.length → D)
    (sourceLocal :
      Fin (Concrete.Elaboration.exactScopeWires input region).length → D) :
    severExtendedEnv original region sourceOuter sourceLocal ∘
        (collapse.extend region).indexMap =
      severExtendedEnv expanded region
        (sourceOuter ∘ collapse.indexMap)
        (severTargetLocalEnv collapse region sourceOuter sourceLocal) := by
  funext targetIndex
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend expanded region) targetIndex
  have hrecover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend expanded region).symm
      split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have hindex := collapse.extend_index_inherited region
      originalExtendedNodup inherited
    simp only [Function.comp_apply, severExtendedEnv, extendWireEnv]
    rw [hindex]
    simp [Function.comp_def]
  · simp [severTargetLocalEnv, severExtendedEnv, Function.comp_def,
      extendWireEnv]

private noncomputable def severSourceLocalEnv
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope)
    (targetLocal : Fin (Concrete.Elaboration.exactScopeWires
      (severWireRaw input wire keep) region).length → D) :
    Fin (Concrete.Elaboration.exactScopeWires input region).length → D :=
  targetLocal ∘ Fin.cast
    (severWireRaw_exactScopeWires_length_of_ne input wire keep region hne).symm

private theorem severExtendedEnv_uncollapse_of_ne
    (collapse : SeverContextCollapse input wire keep expanded original)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope)
    (originalExtendedNodup : (original.extend region).Nodup)
    (sourceOuter : Fin original.length → D)
    (targetOuter : Fin expanded.length → D)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (targetLocal : Fin (Concrete.Elaboration.exactScopeWires
      (severWireRaw input wire keep) region).length → D) :
    severExtendedEnv original region sourceOuter
          (severSourceLocalEnv input wire keep region hne targetLocal) ∘
        (collapse.extend region).indexMap =
      severExtendedEnv expanded region targetOuter targetLocal := by
  funext targetIndex
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend expanded region) targetIndex
  have hrecover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend expanded region).symm
      split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have hindex := collapse.extend_index_inherited region
      originalExtendedNodup inherited
    simp only [Function.comp_apply, severExtendedEnv, extendWireEnv]
    rw [hindex]
    simpa [Function.comp_def] using congrFun outerAgrees inherited
  · have hindex := collapse.extend_index_local_of_ne region hne
      originalExtendedNodup localIndex
    simp only [Function.comp_apply, severExtendedEnv, extendWireEnv]
    rw [hindex]
    simp [severSourceLocalEnv, Function.comp_def]

private theorem severWireRaw_resolvePort?_collapse
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (expanded : Concrete.Elaboration.WireContext
      (severWireRaw input wire keep))
    (original : Concrete.Elaboration.WireContext input)
    (collapse : SeverContextCollapse input wire keep expanded original)
    (originalNodup : original.Nodup)
    (inputDisjoint : input.WireEndpointsAreDisjoint)
    (node : Fin input.nodeCount) (port : CPort) :
    Concrete.Elaboration.resolvePort? input original node port =
      (Concrete.Elaboration.resolvePort? (severWireRaw input wire keep)
        expanded node port).map collapse.indexMap := by
  exact Concrete.Elaboration.resolvePort?_map_of_occurrence
    expanded original node node
    (severWireCollapse input wire keep) collapse.indexMap
    originalNodup collapse.get collapse.mem
    (fun candidate endpointPort occurs =>
      severWireRaw_endpointOccurs_collapse input wire keep candidate
        ⟨node, endpointPort⟩ occurs)
    (fun source endpointPort occurs =>
      severWireRaw_endpointOccurs_lift input wire source keep
        ⟨node, endpointPort⟩ occurs)
    inputDisjoint port

private theorem severWireRaw_compileNode?_collapse
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (expanded : Concrete.Elaboration.WireContext
      (severWireRaw input wire keep))
    (original : Concrete.Elaboration.WireContext input)
    (collapse : SeverContextCollapse input wire keep expanded original)
    (binders : Concrete.Elaboration.BinderContext input rels)
    (originalNodup : original.Nodup)
    (inputDisjoint : input.WireEndpointsAreDisjoint)
    (node : Fin input.nodeCount) :
    Concrete.Elaboration.compileNode?  input original binders node =
      (Concrete.Elaboration.compileNode?
        (severWireRaw input wire keep) expanded binders node).map
          (Item.renameWires collapse.indexMap) := by
  have hports : ∀ port,
      Concrete.Elaboration.resolvePort? input original node port =
        (Concrete.Elaboration.resolvePort? (severWireRaw input wire keep)
          expanded node port).map collapse.indexMap :=
    fun port => severWireRaw_resolvePort?_collapse input wire keep
      expanded original collapse originalNodup inputDisjoint node port
  cases hnode : input.nodes node with
  | identity region arity =>
      simp only [Concrete.Elaboration.compileNode?, hnode,
        severWireRaw_nodes]
      have harguments := Concrete.Elaboration.resolvePorts?_map
        expanded original node node collapse.indexMap arity
        (fun index => .arg index) hports
      rw [harguments]
      cases hexpanded : Concrete.Elaboration.resolvePorts?
          (severWireRaw input wire keep) expanded node arity
          (fun index => .arg index) <;>
        simp [Item.renameWires, Function.comp_def]
  | atom region binder =>
      simp only [Concrete.Elaboration.compileNode?, hnode,
        severWireRaw_nodes]
      cases hrelation : binders binder with
      | none => simp
      | some relation =>
          cases relation with
          | mk arity relation =>
              have harguments := Concrete.Elaboration.resolvePorts?_map
                expanded original node node collapse.indexMap arity
                (fun index => .arg index) hports
              dsimp
              rw [harguments]
              cases hexpanded : Concrete.Elaboration.resolvePorts?
                  (severWireRaw input wire keep) expanded node arity
                  (fun index => .arg index) <;>
                simp [Item.renameWires,
                  Function.comp_def]
@[simp] private theorem severWireRaw_localOccurrences
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount) :
    Concrete.Elaboration.localOccurrences (severWireRaw input wire keep) region =
      Concrete.Elaboration.localOccurrences input region := by
  unfold Concrete.Elaboration.localOccurrences
  simp only [severWireRaw_nodeCount, severWireRaw_regionCount,
    severWireRaw_nodes, severWireRaw_regions]
  rfl

private theorem severWireWireTransport_transportBoundary
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (boundary : List (Fin input.wireCount))
    (sourceRoot : ∀ candidate, candidate ∈ boundary →
      (input.wires candidate).scope = input.root) :
    (severWireWireTransport input wire keep).transportBoundary boundary =
      some (boundary.map Fin.castSucc) := by
  apply WireTransport.transportBoundary_eq_map
  intro candidate hmember
  unfold severWireWireTransport WireTransport.append
    WireTransport.rootFiltered
  dsimp only
  change (if ((severWireRaw input wire keep).wires candidate.castSucc).scope =
      (severWireRaw input wire keep).root then some candidate.castSucc
    else none) = some candidate.castSucc
  rw [severWireRaw_oldWire_scope, severWireRaw_root,
    sourceRoot candidate hmember]
  simp

private def severWireRawOpen (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    Concrete.OpenDiagram where
  diagram := severWireRaw source.diagram wire keep
  boundary := source.boundary.map Fin.castSucc

private theorem severWireRawOpen_exposedWires
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    (severWireRawOpen source wire keep).exposedWires =
      source.exposedWires.map Fin.castSucc := by
  unfold severWireRawOpen Concrete.OpenDiagram.exposedWires
  have hinjective : Function.Injective
      (Fin.castSucc : Fin source.diagram.wireCount →
        Fin (source.diagram.wireCount + 1)) := by
    intro left right equality
    apply Fin.ext
    exact congrArg
      (fun value : Fin (source.diagram.wireCount + 1) => value.val) equality
  exact eraseDups_map_injective_soundness Fin.castSucc hinjective _

private theorem severWireRawOpen_wellFormed
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (htarget : (severWireRaw source.val.diagram wire keep).WellFormed
      ) :
    (severWireRawOpen source.val wire keep).WellFormed  where
  diagram_well_formed := htarget
  boundary_is_root_scoped := by
    intro targetWire hmember
    change targetWire ∈ source.val.boundary.map Fin.castSucc at hmember
    rcases List.mem_map.mp hmember with
      ⟨sourceWire, hsourceWire, equality⟩
    subst targetWire
    change ((severWireRaw source.val.diagram wire keep).wires
      sourceWire.castSucc).scope =
        (severWireRaw source.val.diagram wire keep).root
    rw [severWireRaw_oldWire_scope, severWireRaw_root]
    exact source.property.boundary_is_root_scoped sourceWire hsourceWire

private theorem severWireRawOpen_hiddenWires
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    (severWireRawOpen source wire keep).hiddenWires =
      source.hiddenWires.map Fin.castSucc ++
        if source.diagram.root = (source.diagram.wires wire).scope then
          [Fin.last source.diagram.wireCount]
        else [] := by
  unfold Concrete.OpenDiagram.hiddenWires
  change List.filter
      (fun candidate => decide
        (candidate ∉ (severWireRawOpen source wire keep).exposedWires))
      (Concrete.Elaboration.exactScopeWires
        (severWireRaw source.diagram wire keep) source.diagram.root) = _
  rw [severWireRaw_exactScopeWires, severWireRawOpen_exposedWires]
  have hold :
      List.filter
          (fun candidate => decide
            (candidate ∉ source.exposedWires.map Fin.castSucc))
          ((Concrete.Elaboration.exactScopeWires source.diagram
            source.diagram.root).map Fin.castSucc) =
        source.hiddenWires.map Fin.castSucc := by
    unfold Concrete.OpenDiagram.hiddenWires
    rw [List.filter_map]
    apply congrArg (List.map Fin.castSucc)
    apply congrArg (fun predicate =>
      List.filter predicate
        (Concrete.Elaboration.exactScopeWires source.diagram
          source.diagram.root))
    funext candidate
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hnotMap hmemSource
      exact hnotMap (List.mem_map.mpr ⟨candidate, hmemSource, rfl⟩)
    · intro hnotSource hmemMap
      rcases List.mem_map.mp hmemMap with ⟨old, hold, equality⟩
      have : old = candidate := by
        apply Fin.ext
        exact congrArg
          (fun value : Fin (source.diagram.wireCount + 1) => value.val)
          equality
      exact hnotSource (by simpa [this] using hold)
  by_cases hscope :
      source.diagram.root = (source.diagram.wires wire).scope
  · rw [if_pos hscope]
    have hsplit := List.filter_append
      (p := fun candidate => decide
        (candidate ∉ source.exposedWires.map Fin.castSucc))
      ((Concrete.Elaboration.exactScopeWires source.diagram
        source.diagram.root).map Fin.castSucc)
      [Fin.last source.diagram.wireCount]
    calc
      _ = List.filter
            (fun candidate => decide
              (candidate ∉ source.exposedWires.map Fin.castSucc))
            ((Concrete.Elaboration.exactScopeWires source.diagram
              source.diagram.root).map Fin.castSucc) ++
          List.filter
            (fun candidate => decide
              (candidate ∉ source.exposedWires.map Fin.castSucc))
            [Fin.last source.diagram.wireCount] := hsplit
      _ = source.hiddenWires.map Fin.castSucc ++
          [Fin.last source.diagram.wireCount] := by
        rw [hold]
        congr 1
        apply List.filter_eq_self.mpr
        intro fresh hmem
        simp only [List.mem_singleton] at hmem
        subst fresh
        apply decide_eq_true
        intro hexposed
        rcases List.mem_map.mp hexposed with ⟨old, _, equality⟩
        have hvalue := congrArg
          (fun value : Fin (source.diagram.wireCount + 1) => value.val)
          equality
        simp only [Fin.val_last, Fin.val_castSucc] at hvalue
        omega
  · rw [if_neg hscope]
    simp only [List.append_nil]
    change List.filter
        (fun candidate => decide
          (candidate ∉ source.exposedWires.map Fin.castSucc))
        ((Concrete.Elaboration.exactScopeWires source.diagram
          source.diagram.root).map Fin.castSucc) =
      source.hiddenWires.map Fin.castSucc
    exact hold

private theorem severWireRawOpen_rootWires
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    (severWireRawOpen source wire keep).rootWires =
      source.rootWires.map Fin.castSucc ++
        if source.diagram.root = (source.diagram.wires wire).scope then
          [Fin.last source.diagram.wireCount]
        else [] := by
  unfold Concrete.OpenDiagram.rootWires
  rw [severWireRawOpen_exposedWires, severWireRawOpen_hiddenWires,
    List.map_append]
  split <;> simp only [List.append_assoc, List.append_nil] <;> rfl

/-- The compiler context for the severed open root is exactly the source
context with the fresh split identity collapsed back to its source identity.
This is deliberately non-injective: endpoint partitioning changes identity
multiplicity, not the incidence represented by either compiled occurrence. -/
private noncomputable def severWireRawOpen_rootCollapse
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (htarget : (severWireRaw source.val.diagram wire keep).WellFormed
      ) :
    SeverContextCollapse source.val.diagram wire keep
      (severWireRawOpen source.val wire keep).rootWires
      source.val.rootWires :=
  .ofMem (by
    intro candidate
    rw [Concrete.OpenDiagram.mem_rootWires_iff source.val source.property]
    constructor
    · intro hscope
      apply (Concrete.OpenDiagram.mem_rootWires_iff
        (severWireRawOpen source.val wire keep)
        (severWireRawOpen_wellFormed source wire keep htarget) candidate).2
      change ((severWireRaw source.val.diagram wire keep).wires candidate).scope =
        (severWireRaw source.val.diagram wire keep).root
      rw [severWireRaw_scope_collapse, severWireRaw_root]
      exact hscope
    · intro hmember
      have hscope := (Concrete.OpenDiagram.mem_rootWires_iff
        (severWireRawOpen source.val wire keep)
        (severWireRawOpen_wellFormed source wire keep htarget) candidate).1
        hmember
      change ((severWireRaw source.val.diagram wire keep).wires candidate).scope =
        (severWireRaw source.val.diagram wire keep).root at hscope
      rwa [severWireRaw_scope_collapse, severWireRaw_root] at hscope)

private theorem severWireRawOpen_rootCollapse_source_nodup
    (source : Concrete.CheckedOpen ) :
    source.val.rootWires.Nodup :=
  source.val.rootWires_nodup

private def severExposedIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    Fin (severWireRawOpen source wire keep).exposedWires.length →
      Fin source.exposedWires.length :=
  Fin.cast (by
    exact (congrArg List.length
      (severWireRawOpen_exposedWires source wire keep)).trans
        (List.length_map (as := source.exposedWires) Fin.castSucc))

private theorem severExposedIndex_get
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (index : Fin (severWireRawOpen source wire keep).exposedWires.length) :
    source.exposedWires.get (severExposedIndex source wire keep index) =
      severWireCollapse source.diagram wire keep
        ((severWireRawOpen source wire keep).exposedWires.get index) := by
  let equality := severWireRawOpen_exposedWires source wire keep
  have hget := listGet_cast_of_eq equality index
  calc
    source.exposedWires.get (severExposedIndex source wire keep index) =
        severWireCollapse source.diagram wire keep
          ((source.exposedWires.map Fin.castSucc).get
            (Fin.cast (congrArg List.length equality) index)) := by
      simp [severExposedIndex, List.get_eq_getElem, severWireCollapse]
    _ = severWireCollapse source.diagram wire keep
          ((severWireRawOpen source wire keep).exposedWires.get index) :=
      congrArg (severWireCollapse source.diagram wire keep) hget.symm

private noncomputable def severHiddenIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (hne : source.diagram.root ≠ (source.diagram.wires wire).scope) :
    Fin (severWireRawOpen source wire keep).hiddenWires.length →
      Fin source.hiddenWires.length :=
  Fin.cast (by
    have equality := severWireRawOpen_hiddenWires source wire keep
    rw [if_neg hne, List.append_nil] at equality
    exact (congrArg List.length equality).trans
      (List.length_map (as := source.hiddenWires) Fin.castSucc))

private theorem severHiddenIndex_get
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (hne : source.diagram.root ≠ (source.diagram.wires wire).scope)
    (index : Fin (severWireRawOpen source wire keep).hiddenWires.length) :
    source.hiddenWires.get (severHiddenIndex source wire keep hne index) =
      severWireCollapse source.diagram wire keep
        ((severWireRawOpen source wire keep).hiddenWires.get index) := by
  have equality := severWireRawOpen_hiddenWires source wire keep
  rw [if_neg hne, List.append_nil] at equality
  have hget := listGet_cast_of_eq equality index
  calc
    source.hiddenWires.get (severHiddenIndex source wire keep hne index) =
        severWireCollapse source.diagram wire keep
          ((source.hiddenWires.map Fin.castSucc).get
            (Fin.cast (congrArg List.length equality) index)) := by
      simp [severHiddenIndex, List.get_eq_getElem, severWireCollapse]
    _ = severWireCollapse source.diagram wire keep
          ((severWireRawOpen source wire keep).hiddenWires.get index) :=
      congrArg (severWireCollapse source.diagram wire keep) hget.symm

private theorem severRootCollapse_index_exposed
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (index : Fin (severWireRawOpen source.val wire keep).exposedWires.length) :
    let collapse := severWireRawOpen_rootCollapse source wire keep targetWellFormed
    collapse.indexMap
        (Fin.cast List.length_append.symm
          (Fin.castAdd
            (severWireRawOpen source.val wire keep).hiddenWires.length index)) =
      Fin.cast List.length_append.symm
        (Fin.castAdd source.val.hiddenWires.length
          (severExposedIndex source.val wire keep index)) := by
  dsimp only
  let collapse := severWireRawOpen_rootCollapse source wire keep targetWellFormed
  let targetIndex : Fin (severWireRawOpen source.val wire keep).rootWires.length :=
    Fin.cast List.length_append.symm
      (Fin.castAdd
        (severWireRawOpen source.val wire keep).hiddenWires.length index)
  let sourceIndex : Fin source.val.rootWires.length :=
    Fin.cast List.length_append.symm
      (Fin.castAdd source.val.hiddenWires.length
        (severExposedIndex source.val wire keep index))
  change collapse.indexMap targetIndex = sourceIndex
  apply Fin.ext
  apply (List.getElem_inj source.val.rootWires_nodup).mp
  simpa only [List.get_eq_getElem] using
    (show source.val.rootWires.get (collapse.indexMap targetIndex) =
        source.val.rootWires.get sourceIndex by
      calc
        source.val.rootWires.get (collapse.indexMap targetIndex) =
            severWireCollapse source.val.diagram wire keep
              ((severWireRawOpen source.val wire keep).rootWires.get targetIndex) :=
          collapse.get targetIndex
        _ = severWireCollapse source.val.diagram wire keep
              ((severWireRawOpen source.val wire keep).exposedWires.get index) := by
          simp [targetIndex, Concrete.OpenDiagram.rootWires]
        _ = source.val.exposedWires.get
              (severExposedIndex source.val wire keep index) :=
          (severExposedIndex_get source.val wire keep index).symm
        _ = source.val.rootWires.get sourceIndex := by
          simp [sourceIndex, Concrete.OpenDiagram.rootWires])

private theorem severRootCollapse_index_hidden_of_ne
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (hne : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    (index : Fin (severWireRawOpen source.val wire keep).hiddenWires.length) :
    let collapse := severWireRawOpen_rootCollapse source wire keep targetWellFormed
    collapse.indexMap
        (Fin.cast List.length_append.symm
          (Fin.natAdd
            (severWireRawOpen source.val wire keep).exposedWires.length index)) =
      Fin.cast List.length_append.symm
        (Fin.natAdd source.val.exposedWires.length
          (severHiddenIndex source.val wire keep hne index)) := by
  dsimp only
  let collapse := severWireRawOpen_rootCollapse source wire keep targetWellFormed
  let targetIndex : Fin (severWireRawOpen source.val wire keep).rootWires.length :=
    Fin.cast List.length_append.symm
      (Fin.natAdd
        (severWireRawOpen source.val wire keep).exposedWires.length index)
  let sourceIndex : Fin source.val.rootWires.length :=
    Fin.cast List.length_append.symm
      (Fin.natAdd source.val.exposedWires.length
        (severHiddenIndex source.val wire keep hne index))
  change collapse.indexMap targetIndex = sourceIndex
  apply Fin.ext
  apply (List.getElem_inj source.val.rootWires_nodup).mp
  simpa only [List.get_eq_getElem] using
    (show source.val.rootWires.get (collapse.indexMap targetIndex) =
        source.val.rootWires.get sourceIndex by
      calc
        source.val.rootWires.get (collapse.indexMap targetIndex) =
            severWireCollapse source.val.diagram wire keep
              ((severWireRawOpen source.val wire keep).rootWires.get targetIndex) :=
          collapse.get targetIndex
        _ = severWireCollapse source.val.diagram wire keep
              ((severWireRawOpen source.val wire keep).hiddenWires.get index) := by
          simp [targetIndex, Concrete.OpenDiagram.rootWires]
        _ = source.val.hiddenWires.get
              (severHiddenIndex source.val wire keep hne index) :=
          (severHiddenIndex_get source.val wire keep hne index).symm
        _ = source.val.rootWires.get sourceIndex := by
          simp [sourceIndex, Concrete.OpenDiagram.rootWires])

private noncomputable def severTargetHiddenEnv
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (sourceOuter : Fin source.val.exposedWires.length → D)
    (sourceHidden : Fin source.val.hiddenWires.length → D) :
    Fin (severWireRawOpen source.val wire keep).hiddenWires.length → D :=
  fun index =>
    Concrete.Elaboration.rootEnvironment source.val.exposedWires
      source.val.hiddenWires sourceOuter sourceHidden
      ((severWireRawOpen_rootCollapse source wire keep targetWellFormed).indexMap
        (Fin.cast List.length_append.symm
          (Fin.natAdd
            (severWireRawOpen source.val wire keep).exposedWires.length index)))

private theorem rootEnvironment_exposed_soundness
    {diagram : Concrete.Diagram}
    (ambient locals : Concrete.Elaboration.WireContext diagram)
    (outer : Fin ambient.length → D) (localEnv : Fin locals.length → D)
    (index : Fin ambient.length) :
    Concrete.Elaboration.rootEnvironment ambient locals outer localEnv
        (Fin.cast List.length_append.symm
          (Fin.castAdd locals.length index)) = outer index := by
  simp [Concrete.Elaboration.rootEnvironment, extendWireEnv]

private theorem rootEnvironment_hidden_soundness
    {diagram : Concrete.Diagram}
    (ambient locals : Concrete.Elaboration.WireContext diagram)
    (outer : Fin ambient.length → D) (localEnv : Fin locals.length → D)
    (index : Fin locals.length) :
    Concrete.Elaboration.rootEnvironment ambient locals outer localEnv
        (Fin.cast List.length_append.symm
          (Fin.natAdd ambient.length index)) = localEnv index := by
  simp [Concrete.Elaboration.rootEnvironment, extendWireEnv]

private theorem severRootEnvironment_collapse
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (sourceOuter : Fin source.val.exposedWires.length → D)
    (targetOuter :
      Fin (severWireRawOpen source.val wire keep).exposedWires.length → D)
    (outerAgrees : sourceOuter ∘ severExposedIndex source.val wire keep =
      targetOuter)
    (sourceHidden : Fin source.val.hiddenWires.length → D) :
    Concrete.Elaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceHidden ∘
        (severWireRawOpen_rootCollapse source wire keep targetWellFormed).indexMap =
      Concrete.Elaboration.rootEnvironment
        (severWireRawOpen source.val wire keep).exposedWires
        (severWireRawOpen source.val wire keep).hiddenWires targetOuter
        (severTargetHiddenEnv source wire keep targetWellFormed sourceOuter
          sourceHidden) := by
  funext targetIndex
  let split := Fin.cast List.length_append targetIndex
  have hrecover : Fin.cast List.length_append.symm split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · have hindex := severRootCollapse_index_exposed source wire keep
      targetWellFormed exposed
    dsimp only at hindex
    simp only [Function.comp_apply]
    calc
      _ = Concrete.Elaboration.rootEnvironment source.val.exposedWires
            source.val.hiddenWires sourceOuter sourceHidden
            (Fin.cast List.length_append.symm
              (Fin.castAdd source.val.hiddenWires.length
                (severExposedIndex source.val wire keep exposed))) :=
        congrArg (Concrete.Elaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceHidden) hindex
      _ = sourceOuter (severExposedIndex source.val wire keep exposed) :=
        rootEnvironment_exposed_soundness _ _ _ _ _
      _ = targetOuter exposed := congrFun outerAgrees exposed
      _ = _ := (rootEnvironment_exposed_soundness _ _ _ _ _).symm
  · simp only [Function.comp_apply]
    calc
      _ = severTargetHiddenEnv source wire keep targetWellFormed sourceOuter
          sourceHidden hidden := rfl
      _ = _ := (rootEnvironment_hidden_soundness _ _ _ _ _).symm

private noncomputable def severSourceHiddenEnv
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (hne : source.diagram.root ≠ (source.diagram.wires wire).scope)
    (targetHidden :
      Fin (severWireRawOpen source wire keep).hiddenWires.length → D) :
    Fin source.hiddenWires.length → D :=
  targetHidden ∘ Fin.cast (by
    have equality := severWireRawOpen_hiddenWires source wire keep
    rw [if_neg hne, List.append_nil] at equality
    exact ((congrArg List.length equality).trans
      (List.length_map (as := source.hiddenWires) Fin.castSucc)).symm)

private theorem severRootEnvironment_uncollapse_of_ne
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (hne : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    (sourceOuter : Fin source.val.exposedWires.length → D)
    (targetOuter :
      Fin (severWireRawOpen source.val wire keep).exposedWires.length → D)
    (outerAgrees : sourceOuter ∘ severExposedIndex source.val wire keep =
      targetOuter)
    (targetHidden :
      Fin (severWireRawOpen source.val wire keep).hiddenWires.length → D) :
    Concrete.Elaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter
          (severSourceHiddenEnv source.val wire keep hne targetHidden) ∘
        (severWireRawOpen_rootCollapse source wire keep targetWellFormed).indexMap =
      Concrete.Elaboration.rootEnvironment
        (severWireRawOpen source.val wire keep).exposedWires
        (severWireRawOpen source.val wire keep).hiddenWires targetOuter
        targetHidden := by
  funext targetIndex
  let split := Fin.cast List.length_append targetIndex
  have hrecover : Fin.cast List.length_append.symm split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · have hindex := severRootCollapse_index_exposed source wire keep
      targetWellFormed exposed
    dsimp only at hindex
    simp only [Function.comp_apply]
    calc
      _ = Concrete.Elaboration.rootEnvironment source.val.exposedWires
            source.val.hiddenWires sourceOuter
            (severSourceHiddenEnv source.val wire keep hne targetHidden)
            (Fin.cast List.length_append.symm
              (Fin.castAdd source.val.hiddenWires.length
                (severExposedIndex source.val wire keep exposed))) :=
        congrArg (Concrete.Elaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter
          (severSourceHiddenEnv source.val wire keep hne targetHidden)) hindex
      _ = sourceOuter (severExposedIndex source.val wire keep exposed) :=
        rootEnvironment_exposed_soundness _ _ _ _ _
      _ = targetOuter exposed := congrFun outerAgrees exposed
      _ = _ := (rootEnvironment_exposed_soundness _ _ _ _ _).symm
  · have hindex := severRootCollapse_index_hidden_of_ne source wire keep
      targetWellFormed hne hidden
    dsimp only at hindex
    simp only [Function.comp_apply]
    calc
      _ = Concrete.Elaboration.rootEnvironment source.val.exposedWires
            source.val.hiddenWires sourceOuter
            (severSourceHiddenEnv source.val wire keep hne targetHidden)
            (Fin.cast List.length_append.symm
              (Fin.natAdd source.val.exposedWires.length
                (severHiddenIndex source.val wire keep hne hidden))) :=
        congrArg (Concrete.Elaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter
          (severSourceHiddenEnv source.val wire keep hne targetHidden)) hindex
      _ = (severSourceHiddenEnv source.val wire keep hne targetHidden)
          (severHiddenIndex source.val wire keep hne hidden) :=
        rootEnvironment_hidden_soundness _ _ _ _ _
      _ = targetHidden hidden := by
        simp [severSourceHiddenEnv, severHiddenIndex]
      _ = _ := (rootEnvironment_hidden_soundness _ _ _ _ _).symm

private def severDirection : Orientation →
    Concrete.Elaboration.SimulationDirection
  | .forward => .forward
  | .backward => .backward

private def severDepthAllowed
    (direction : Concrete.Elaboration.SimulationDirection) (depth : Nat) : Prop :=
  match direction with
  | .forward => depth % 2 = 0
  | .backward => depth % 2 = 1

/-- A local compiler direction is admissible exactly when following any
concrete route from that region to the split wire's binding site makes the
split weakening covariant.  The universal formulation is vacuous off the
ancestor chain and composes directly through cut and bubble children. -/
private def severAllowed (input : Concrete.Diagram)
    (site : Fin input.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (region : Fin input.regionCount) : Prop :=
  ∀ {path depth} (route : Concrete.Splice.RegionRoute input region site path),
    route.HasCutDepth depth → severDepthAllowed direction depth

private theorem severAllowed_cut
    (input : Concrete.Diagram) (site : Fin input.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (child parent : Fin input.regionCount)
    (childKind : input.regions child = .cut parent)
    (allowed : severAllowed input site direction parent) :
    severAllowed input site direction.flip child := by
  intro path depth route routeDepth
  have hparent : (input.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, hposition⟩ := indexOf?_complete
    ((Concrete.Elaboration.mem_localOccurrences_child input parent child).2
      hparent)
  let parentRoute :=
    Concrete.Splice.RegionRoute.step hparent position hposition route
  have parentDepth : parentRoute.HasCutDepth (depth + 1) := by
    exact Concrete.Splice.RegionRoute.HasCutDepth.cut
      (hparent := hparent) (position := position) (hposition := hposition)
      childKind routeDepth
  have := allowed parentRoute parentDepth
  cases direction <;> simp [severDepthAllowed] at this ⊢ <;> omega

private theorem severAllowed_bubble
    (input : Concrete.Diagram) (site : Fin input.regionCount)
    (direction : Concrete.Elaboration.SimulationDirection)
    (child parent : Fin input.regionCount) (arity : Nat)
    (childKind : input.regions child = .bubble parent arity)
    (allowed : severAllowed input site direction parent) :
    severAllowed input site direction child := by
  intro path depth route routeDepth
  have hparent : (input.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, hposition⟩ := indexOf?_complete
    ((Concrete.Elaboration.mem_localOccurrences_child input parent child).2
      hparent)
  let parentRoute :=
    Concrete.Splice.RegionRoute.step hparent position hposition route
  have parentDepth : parentRoute.HasCutDepth depth := by
    exact Concrete.Splice.RegionRoute.HasCutDepth.bubble
      (hparent := hparent) (position := position) (hposition := hposition)
      childKind routeDepth
  exact allowed parentRoute parentDepth

private theorem severAllowed_root
    (source : Concrete.CheckedOpen )
    (site : Fin source.val.diagram.regionCount)
    (orientation : Orientation)
    (polarity : erasurePolarity orientation
      (concreteCutDepth source.val.diagram site)) :
    severAllowed source.val.diagram site (severDirection orientation)
      source.val.diagram.root := by
  intro path depth route routeDepth
  let view := Classical.choice
    (Concrete.Splice.openSiteView_complete source site)
  have pathEq : path = view.path :=
    Concrete.Splice.Input.RegionRoute.path_unique
      source.property.diagram_well_formed route view.route
  subst path
  have routeEq : route = view.route := Subsingleton.elim _ _
  subst route
  have depthEq : depth = view.focus.context.cutDepth :=
    regionRoute_cutDepth_unique routeDepth view.cutDepth
  subst depth
  rw [← openSiteView_concreteCutDepth_eq view]
  cases orientation <;> exact polarity

private theorem severAllowed_backward_ne_site
    (input : Concrete.Diagram) (site region : Fin input.regionCount)
    (allowed : severAllowed input site .backward region) :
    region ≠ site := by
  intro equality
  subst region
  have impossible := allowed (Concrete.Splice.RegionRoute.here site)
    (Concrete.Splice.RegionRoute.HasCutDepth.here site)
  simp [severDepthAllowed] at impossible

private noncomputable def severWireSimulation
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (model : Model)
    :
    Concrete.Elaboration.ConcreteSemanticSimulation
      source.val.diagram (severWireRaw source.val.diagram wire keep) model  where
  source_wellFormed := source.property.diagram_well_formed
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun _ => False
  occurrenceMap := fun _ _ occurrence => occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child hparent
    rw [severWireRaw_regions]
    cases hkind : source.val.diagram.regions child <;> simp [hkind, id]
  localOccurrences_map := by
    intro region regular
    rw [severWireRaw_localOccurrences]
    simp
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    Concrete.Elaboration.IdentityBinderWitness
      (sourceRels := sourceRels) (targetRels := targetRels)
      source.val.diagram (severWireRaw source.val.diagram wire keep)
      sourceBinders targetBinders
  relationMap := fun witness =>
    Concrete.Elaboration.IdentityBinderWitness.relationMap witness
  binders_empty := {
    relationContexts_eq := rfl
    binders_eq := HEq.rfl
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    exact ⟨rfl, HEq.rfl⟩
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [Concrete.Elaboration.IdentityBinderWitness.relationMap,
      Concrete.Elaboration.identityRelationRenaming] using
        (RelationRenaming.lift_id_fun
          (source := sourceRels) arity).symm
  Allowed := severAllowed source.val.diagram
    (source.val.diagram.wires wire).scope
  allowed_cut := by
    intro direction child parent childKind _ allowed
    exact severAllowed_cut source.val.diagram
      (source.val.diagram.wires wire).scope direction child parent childKind allowed
  allowed_bubble := by
    intro direction child parent arity childKind _ allowed
    exact severAllowed_bubble source.val.diagram
      (source.val.diagram.wires wire).scope direction child parent arity childKind
      allowed
  ContextWitness := fun original expanded =>
    SeverContextCollapse source.val.diagram wire keep expanded original
  AtRegion := fun _ _ => True
  indexRelation := fun collapse =>
    Concrete.Elaboration.ContextIndexRelation.backwardMap collapse.indexMap
  extendContext := fun original expanded collapse region _regular sourceExact targetExact =>
    collapse.extend region
  extendFocusedContext := by
    intro original expanded collapse region atRegion focused sourceExact targetExact
    exact False.elim focused
  at_child := by simp
  at_extended := by simp
  at_focused_child := by
    intro original expanded collapse parent focused sourceExact targetExact child
      atParent sourceParent targetParent
    exact False.elim focused
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget original expanded
      collapse sourceBinders targetBinders binderWitness region atRegion regular
      allowed sourceExact targetExact _ _ _ _ sourceItems targetItems
      sourceCompiled targetCompiled itemSemantics
    refine Concrete.Elaboration.directionalLocalTransport_of_agreement
      direction original expanded region region
      (Concrete.Elaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      (Concrete.Elaboration.ContextIndexRelation.backwardMap
        (collapse.extend region).indexMap)
      model
      (sourceItems.renameRelations
        (Concrete.Elaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems ?_ itemSemantics
    intro sourceOuter targetOuter outerAgrees
    rw [Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap]
      at outerAgrees
    cases direction with
    | forward =>
        intro sourceLocal
        refine ⟨severTargetLocalEnv collapse region sourceOuter sourceLocal, ?_⟩
        apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
          _ _ _).2
        simpa [Concrete.Elaboration.extendedEnvironment, id, ← outerAgrees] using
          (severExtendedEnv_collapse collapse region sourceExact.nodup
            sourceOuter sourceLocal)
    | backward =>
        intro targetLocal
        have hne := severAllowed_backward_ne_site source.val.diagram
          (source.val.diagram.wires wire).scope region allowed
        refine ⟨severSourceLocalEnv source.val.diagram wire keep region hne
          targetLocal, ?_⟩
        apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
          _ _ _).2
        simpa [Concrete.Elaboration.extendedEnvironment, id] using
          (severExtendedEnv_uncollapse_of_ne collapse region hne
            sourceExact.nodup sourceOuter targetOuter outerAgrees targetLocal)
  nodeSemantic := by
    intro sourceRels targetRels direction region original expanded collapse
      atRegion sourceNodup targetNodup sourceBinders targetBinders allowed
      binderWitness sourceNode targetNode regular nodeMapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    change Concrete.Elaboration.ItemSimulation model  direction
      (Concrete.Elaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      (sourceItem.renameRelations
        ((fun relation => relation) : RelationRenaming sourceRels sourceRels))
      targetItem
    rw [Item.renameRelations_id]
    have nodeEq : sourceNode = targetNode := by
      exact Concrete.Elaboration.LocalOccurrence.node.inj nodeMapped
    subst targetNode
    have mapped := severWireRaw_compileNode?_collapse
      source.val.diagram wire keep expanded original collapse sourceBinders sourceNodup
      source.property.diagram_well_formed.wire_endpoints_are_disjoint sourceNode
    rw [sourceCompiled, targetCompiled] at mapped
    have itemEq : sourceItem = targetItem.renameWires collapse.indexMap := by
      simpa using Option.some.inj mapped
    subst sourceItem
    intro sourceEnv targetEnv relEnv environments
    rw [Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap]
      at environments
    have renamed := denoteItem_renameWires model  collapse.indexMap
      sourceEnv relEnv targetItem
    rw [environments] at renamed
    cases direction with
    | forward => exact renamed.mp
    | backward => exact renamed.mpr
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region original
      expanded collapse sourceBinders targetBinders atRegion distinguished
    exact False.elim distinguished

private noncomputable def severWireRootContext
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (model : Model)
    (orientation : Orientation)
    (polarity : erasurePolarity orientation
      (concreteCutDepth source.val.diagram
        (source.val.diagram.wires wire).scope)) :
    let simulation := severWireSimulation source wire keep targetWellFormed
      model
    Concrete.Elaboration.ConcreteSemanticSimulation.RootContextSimulation simulation
      (severDirection orientation)
      source.val.exposedWires source.val.hiddenWires
      (severWireRawOpen source.val wire keep).exposedWires
      (severWireRawOpen source.val wire keep).hiddenWires := by
  let simulation := severWireSimulation source wire keep targetWellFormed
    model
  let collapse := severWireRawOpen_rootCollapse source wire keep targetWellFormed
  refine {
    outer := Concrete.Elaboration.ContextIndexRelation.backwardMap
      (severExposedIndex source.val wire keep)
    context := ?_
    atRoot := True.intro
    atRootChild := by
      intro regular child parent
      trivial
    atFocusedRootChild := by
      intro focused
      exact False.elim focused
    transport := ?_
    focusedRootKernel := ?_
  }
  · simpa only [Concrete.OpenDiagram.rootWires] using collapse
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    refine Concrete.Elaboration.directionalRootTransport_of_agreement
      (severDirection orientation)
      source.val.exposedWires source.val.hiddenWires
      (severWireRawOpen source.val wire keep).exposedWires
      (severWireRawOpen source.val wire keep).hiddenWires
      (Concrete.Elaboration.ContextIndexRelation.backwardMap
        (severExposedIndex source.val wire keep))
      (Concrete.Elaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      model
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems ?_ itemSemantics
    intro sourceOuter targetOuter outerAgrees
    rw [Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap]
      at outerAgrees
    cases orientation with
    | forward =>
        intro sourceHidden
        refine ⟨severTargetHiddenEnv source wire keep targetWellFormed sourceOuter
          sourceHidden, ?_⟩
        apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
          _ _ _).2
        simpa only [Concrete.OpenDiagram.rootWires] using
          (severRootEnvironment_collapse source wire keep targetWellFormed
            sourceOuter targetOuter outerAgrees sourceHidden)
    | backward =>
        intro targetHidden
        have hne := severAllowed_backward_ne_site source.val.diagram
          (source.val.diagram.wires wire).scope source.val.diagram.root allowed
        refine ⟨severSourceHiddenEnv source.val wire keep hne targetHidden, ?_⟩
        apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
          _ _ _).2
        simpa only [Concrete.OpenDiagram.rootWires] using
          (severRootEnvironment_uncollapse_of_ne source wire keep targetWellFormed
            hne sourceOuter targetOuter outerAgrees targetHidden)
  · intro atRoot distinguished
    exact False.elim distinguished

private theorem severBoundaryLengthEq
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    (severWireRawOpen source wire keep).boundary.length =
      source.boundary.length := by
  simp [severWireRawOpen]

private def severSourceExposedIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    Fin source.exposedWires.length →
      Fin (severWireRawOpen source wire keep).exposedWires.length :=
  Fin.cast (by
    exact ((congrArg List.length
      (severWireRawOpen_exposedWires source wire keep)).trans
        (List.length_map (as := source.exposedWires) Fin.castSucc)).symm)

private theorem severExposedIndex_sourceExposedIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (index : Fin source.exposedWires.length) :
    severExposedIndex source wire keep
      (severSourceExposedIndex source wire keep index) = index := by
  apply Fin.ext
  rfl

private theorem severSourceExposedIndex_exposedIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (index : Fin (severWireRawOpen source wire keep).exposedWires.length) :
    severSourceExposedIndex source wire keep
      (severExposedIndex source wire keep index) = index := by
  apply Fin.ext
  rfl

private theorem severBoundaryClass
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (position : Fin source.boundary.length) :
    severExposedIndex source wire keep
        ((severWireRawOpen source wire keep).boundaryClass
          (Fin.cast (severBoundaryLengthEq source wire keep).symm position)) =
      source.boundaryClass position := by
  apply source.boundaryClass_complete
  rw [severExposedIndex_get,
    Concrete.OpenDiagram.boundaryClass_sound]
  simp [severWireRawOpen, List.get_eq_getElem, severWireCollapse]

private theorem severSourceBoundaryClass
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount))
    (position : Fin source.boundary.length) :
    severSourceExposedIndex source wire keep (source.boundaryClass position) =
      (severWireRawOpen source wire keep).boundaryClass
        (Fin.cast (severBoundaryLengthEq source wire keep).symm position) := by
  apply (congrArg (severSourceExposedIndex source wire keep)
    (severBoundaryClass source wire keep position)).symm.trans
  exact severSourceExposedIndex_exposedIndex source wire keep _

private theorem severBoundaryWitness
    (source : Concrete.CheckedOpen )
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed : (severWireRaw source.val.diagram wire keep).WellFormed
      )
    (direction : Concrete.Elaboration.SimulationDirection)
    (model : Model)
    (sourceArgs : Fin source.val.boundary.length → model.Carrier) :
    Concrete.Elaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate
      (Concrete.CheckedOpen.elaborate (⟨severWireRawOpen source.val wire keep,
        severWireRawOpen_wellFormed source wire keep targetWellFormed⟩ :
          Concrete.CheckedOpen ))
      (Concrete.Elaboration.ContextIndexRelation.backwardMap
        (severExposedIndex source.val wire keep))
      model  sourceArgs
      (sourceArgs ∘ Fin.cast (severBoundaryLengthEq source.val wire keep)) := by
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : BoundaryAssignment
          (Concrete.CheckedOpen.elaborate (⟨severWireRawOpen source.val wire keep,
            severWireRawOpen_wellFormed source wire keep targetWellFormed⟩ :
              Concrete.CheckedOpen )) model.Carrier := {
        args := sourceArgs ∘ Fin.cast
          (severBoundaryLengthEq source.val wire keep)
        classes := sourceAssignment.classes ∘
          severExposedIndex source.val wire keep
        agrees := by
          intro targetPosition
          let sourcePosition := Fin.cast
            (severBoundaryLengthEq source.val wire keep) targetPosition
          change sourceAssignment.classes
              (severExposedIndex source.val wire keep
                ((severWireRawOpen source.val wire keep).boundaryClass
                  targetPosition)) = sourceArgs sourcePosition
          have classEq := severBoundaryClass source.val wire keep sourcePosition
          have positionEq : Fin.cast
              (severBoundaryLengthEq source.val wire keep).symm sourcePosition =
              targetPosition := by apply Fin.ext; rfl
          rw [positionEq] at classEq
          rw [classEq]
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          change sourceAssignment.classes
              (source.val.boundaryClass sourcePosition) =
            sourceAssignment.args sourcePosition at sourceAgrees
          rw [sourceArgsEq] at sourceAgrees
          exact sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
        _ _ _).2
      rfl
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘
          severSourceExposedIndex source.val wire keep
        agrees := by
          intro sourcePosition
          change targetAssignment.classes
              (severSourceExposedIndex source.val wire keep
                (source.val.boundaryClass sourcePosition)) =
            sourceArgs sourcePosition
          rw [severSourceBoundaryClass]
          have targetAgrees := targetAssignment.agrees
            (Fin.cast (severBoundaryLengthEq source.val wire keep).symm
              sourcePosition)
          rw [targetArgsEq] at targetAgrees
          exact targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
        _ _ _).2
      funext targetClass
      simp only [sourceAssignment, Function.comp_apply]
      rw [severSourceExposedIndex_exposedIndex]

private def severOperationalOpen
    (source : OperationState )
    (wire : Fin source.diagram.val.wireCount)
    (keep : List (CEndpoint source.diagram.val.nodeCount))
    (targetWellFormed : (severWireRaw source.diagram.val wire keep).WellFormed
      ) : Concrete.CheckedOpen  :=
  ⟨severWireRawOpen source.asCheckedOpen.val wire keep,
    severWireRawOpen_wellFormed source.asCheckedOpen wire keep targetWellFormed⟩

private def severOperationalIso
    {input : Concrete.Checked } {receipt : OperationReceipt input}
    {wire : Fin input.val.wireCount}
    {keep : List (CEndpoint input.val.nodeCount)}
    (realizes : receipt.Realizes (severWireRaw input.val wire keep)
      (severWireProvenance input.val wire keep)
      (severWireWireTransport input.val wire keep))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ candidate, candidate ∈ boundary →
      (input.val.wires candidate).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.OpenIso
      (severWireRawOpen
        (OperationState.asCheckedOpen {
          diagram := input
          boundary := boundary
          boundary_root_scoped := sourceRoot
        }).val wire keep)
      (realizes.rawResultOpen mapped) := by
  apply realizes.operationalIso_to_rawResultOpen htransport
    (boundary.map Fin.castSucc)
  simpa using severWireWireTransport_transportBoundary input.val wire keep
    boundary sourceRoot

/-- Every successful wire-sever receipt has the directed semantics selected by
its checked orientation and the cut polarity of the split wire's binding
scope, at every ordered open boundary. -/
theorem applyWireSever_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (wire : Fin input.val.wireCount)
    (keep : List (CEndpoint input.val.nodeCount))
    (receipt : OperationReceipt input)
    (happly : applyWireSever orientation input wire keep = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyWireSever_realizes happly
  have success := applyWireSever_success orientation input wire keep receipt
    happly
  have targetWellFormed : (severWireRaw input.val wire keep).WellFormed
       := realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      severOperationalOpen {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } wire keep targetWellFormed)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      severOperationalIso realizes boundary sourceRoot mapped htransport)
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target := severOperationalOpen source wire keep targetWellFormed
  let simulation := severWireSimulation source.asCheckedOpen wire keep
    targetWellFormed model
  let rootContext := severWireRootContext source.asCheckedOpen wire keep
    targetWellFormed model  orientation success.1
  have allowed : simulation.Allowed (severDirection orientation)
      source.asCheckedOpen.val.diagram.root := by
    exact severAllowed_root source.asCheckedOpen
      (source.asCheckedOpen.val.diagram.wires wire).scope orientation success.1
  have boundaryWitness := severBoundaryWitness source.asCheckedOpen wire keep
    targetWellFormed (severDirection orientation) model  args
  have semantic :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model  simulation
      (severDirection orientation) rootContext allowed args
      (args ∘ Fin.cast
        (severBoundaryLengthEq source.asCheckedOpen.val wire keep))
      boundaryWitness
  dsimp only
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := semantic sourceDenotes
      simpa [source, target, severDirection, severOperationalOpen] using
        targetDenotes
  | backward =>
      intro targetDenotes
      apply semantic
      simpa [source, target, severDirection, severOperationalOpen] using
        targetDenotes

@[simp] private theorem joinWireRaw_regionCount
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount) :
    (joinWireRaw input outer inner).regionCount = input.regionCount :=
  rfl

@[simp] private theorem joinWireRaw_nodeCount
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount) :
    (joinWireRaw input outer inner).nodeCount = input.nodeCount :=
  rfl

@[simp] private theorem joinWireRaw_root
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount) :
    (joinWireRaw input outer inner).root = input.root :=
  rfl

@[simp] private theorem joinWireRaw_regions
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (region : Fin input.regionCount) :
    (joinWireRaw input outer inner).regions region = input.regions region :=
  rfl

@[simp] private theorem joinWireRaw_nodes
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (node : Fin input.nodeCount) :
    (joinWireRaw input outer inner).nodes node = input.nodes node :=
  rfl

private def joinOuterIndex
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Fin (joinWireRaw input outer inner).wireCount :=
  let domain := joinWireDomain input inner
  domain.index outer (by
    simp [domain, joinWireDomain, distinct])

private theorem joinOuterIndex_origin
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    (joinWireDomain input inner).origin
        (joinOuterIndex input outer inner distinct) = outer := by
  exact (joinWireDomain input inner).origin_index outer (by
    simp [joinWireDomain, distinct])

/-- The total logical wire map of a valid join.  The absorbed identity maps
to the retained identity's dense survivor index; every other identity maps to
its own dense survivor index. -/
def joinWireBoundaryMap
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Fin input.wireCount → Fin (joinWireRaw input outer inner).wireCount :=
  fun source =>
    if hsource : source = inner then
      joinOuterIndex input outer inner distinct
    else
      (joinWireDomain input inner).index source (by
        simp [joinWireDomain, hsource])

private theorem joinWireBoundaryMap_index?
    (input : Concrete.Diagram) (outer inner source : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    (if source = inner then
        (joinWireDomain input inner).index? outer
      else (joinWireDomain input inner).index? source) =
      some (joinWireBoundaryMap input outer inner distinct source) := by
  by_cases hsource : source = inner
  · rw [if_pos hsource]
    simp only [joinWireBoundaryMap, dif_pos hsource]
    exact (joinWireDomain input inner).index?_index outer (by
      simp [joinWireDomain, distinct])
  · rw [if_neg hsource]
    simp only [joinWireBoundaryMap, dif_neg hsource]
    exact (joinWireDomain input inner).index?_index source (by
      simp [joinWireDomain, hsource])

private theorem joinWireWireTransport_image_eq_boundaryMap_of_some
    (input : Concrete.Diagram) (outer inner source : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (mapped : Fin (joinWireRaw input outer inner).wireCount)
    (himage : (joinWireWireTransport input outer inner).image? source =
      some mapped) :
    mapped = joinWireBoundaryMap input outer inner distinct source := by
  unfold joinWireWireTransport WireTransport.rootFiltered at himage
  dsimp only at himage
  change (if source = inner then
      (joinWireDomain input inner).index? outer
    else (joinWireDomain input inner).index? source).bind
      (fun candidate =>
        if ((joinWireRaw input outer inner).wires candidate).scope =
            (joinWireRaw input outer inner).root then
          some candidate
        else none) = some mapped at himage
  obtain ⟨candidate, hcandidate, hfiltered⟩ :=
    Option.bind_eq_some_iff.mp himage
  have hcanonical :=
    joinWireBoundaryMap_index? input outer inner source distinct
  have hcandidateEq : candidate =
      joinWireBoundaryMap input outer inner distinct source :=
    Option.some.inj (hcandidate.symm.trans hcanonical)
  split at hfiltered
  · exact (Option.some.inj hfiltered).symm.trans hcandidateEq
  · contradiction

/-- Pointwise form of successful ordered join transport.  It applies to every
boundary position independently, so repeated source positions remain repeated
and the retained/absorbed pair becomes an ordered alias wherever it occurs. -/
theorem joinWireWireTransport_transportBoundary_get
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (boundary : List (Fin input.wireCount))
    (mapped : List (Fin (joinWireRaw input outer inner).wireCount))
    (htransport :
      (joinWireWireTransport input outer inner).transportBoundary
        boundary = some mapped)
    (index : Fin boundary.length) :
    mapped.get (Fin.cast
        ((joinWireWireTransport input outer inner).transportBoundary_length
          htransport).symm index) =
      joinWireBoundaryMap input outer inner distinct (boundary.get index) := by
  have himage :=
    (joinWireWireTransport input outer inner).transportBoundary_get
      htransport index
  exact joinWireWireTransport_image_eq_boundaryMap_of_some input outer
    inner (boundary.get index) distinct _ himage

/-- Exact normalization of every successful ordered join transport.  No
deduplication occurs: list order and arbitrary repeated positions are
preserved, while every occurrence of the absorbed identity maps to the same
dense identity as the retained wire. -/
theorem joinWireWireTransport_transportBoundary_eq_map
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (boundary : List (Fin input.wireCount))
    (mapped : List (Fin (joinWireRaw input outer inner).wireCount))
    (htransport :
      (joinWireWireTransport input outer inner).transportBoundary
        boundary = some mapped) :
    mapped = boundary.map (joinWireBoundaryMap input outer inner distinct) := by
  have himage : ∀ source, source ∈ boundary →
      (joinWireWireTransport input outer inner).image? source =
        some (joinWireBoundaryMap input outer inner distinct source) := by
    intro source hmember
    obtain ⟨index, hindex⟩ := List.mem_iff_get.mp hmember
    have hpoint :=
      (joinWireWireTransport input outer inner).transportBoundary_get
        htransport index
    have heq := joinWireWireTransport_image_eq_boundaryMap_of_some input
      outer inner (boundary.get index) distinct _ hpoint
    rw [← hindex]
    rw [hpoint, heq]
  have hcanonical :=
    (joinWireWireTransport input outer inner).transportBoundary_eq_map
      (joinWireBoundaryMap input outer inner distinct) himage
  exact Option.some.inj (htransport.symm.trans hcanonical)

private theorem joinWireRaw_outerWire
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    (joinWireRaw input outer inner).wires
        (joinOuterIndex input outer inner distinct) =
      { scope := (input.wires outer).scope
        endpoints := (input.wires outer).endpoints ++
          (input.wires inner).endpoints } := by
  change (if (joinWireDomain input inner).origin
        (joinOuterIndex input outer inner distinct) = outer then
      { scope := (input.wires outer).scope
        endpoints := (input.wires outer).endpoints ++
          (input.wires inner).endpoints }
    else input.wires ((joinWireDomain input inner).origin
      (joinOuterIndex input outer inner distinct))) = _
  rw [joinOuterIndex_origin input outer inner distinct]
  simp

private theorem joinWireRaw_outerEndpointOccurs_iff
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) (endpoint : CEndpoint input.nodeCount) :
    (joinWireRaw input outer inner).EndpointOccurs
        (joinOuterIndex input outer inner distinct) endpoint ↔
      input.EndpointOccurs outer endpoint ∨
        input.EndpointOccurs inner endpoint := by
  unfold Concrete.Diagram.EndpointOccurs
  rw [joinWireRaw_outerWire input outer inner distinct]
  change endpoint ∈
      (input.wires outer).endpoints ++ (input.wires inner).endpoints ↔
    endpoint ∈ (input.wires outer).endpoints ∨
      endpoint ∈ (input.wires inner).endpoints
  exact List.mem_append

private theorem joinWireRaw_wire_of_origin_ne
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (candidate : Fin (joinWireRaw input outer inner).wireCount)
    (hne : (joinWireDomain input inner).origin candidate ≠ outer) :
    (joinWireRaw input outer inner).wires candidate =
      input.wires ((joinWireDomain input inner).origin candidate) := by
  change (if (joinWireDomain input inner).origin candidate = outer then
      { scope := (input.wires outer).scope
        endpoints := (input.wires outer).endpoints ++
          (input.wires inner).endpoints }
    else input.wires ((joinWireDomain input inner).origin candidate)) = _
  rw [if_neg hne]

private theorem joinWireRaw_endpointOccurs_of_origin_ne
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (candidate : Fin (joinWireRaw input outer inner).wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (hne : (joinWireDomain input inner).origin candidate ≠ outer) :
    (joinWireRaw input outer inner).EndpointOccurs candidate endpoint ↔
      input.EndpointOccurs
        ((joinWireDomain input inner).origin candidate) endpoint := by
  unfold Concrete.Diagram.EndpointOccurs
  rw [joinWireRaw_wire_of_origin_ne input outer inner candidate hne]
  rfl

private theorem joinWireRaw_scope
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (candidate : Fin (joinWireRaw input outer inner).wireCount) :
    ((joinWireRaw input outer inner).wires candidate).scope =
      if (joinWireDomain input inner).origin candidate = outer then
        (input.wires outer).scope
      else
        (input.wires
          ((joinWireDomain input inner).origin candidate)).scope := by
  change (if (joinWireDomain input inner).origin candidate = outer then
      { scope := (input.wires outer).scope
        endpoints := (input.wires outer).endpoints ++
          (input.wires inner).endpoints }
    else input.wires
      ((joinWireDomain input inner).origin candidate)).scope = _
  by_cases houter :
      (joinWireDomain input inner).origin candidate = outer
  · rw [if_pos houter, if_pos houter]
  · rw [if_neg houter, if_neg houter]

/-- Every successful wire-join receipt preserves ordered-open semantics. -/
theorem applyWireJoin_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (first second : Fin input.val.wireCount)
    (receipt : OperationReceipt input)
    (happly : applyWireJoin orientation input first second = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  exact WireJoinSoundness.wireJoinReceipt_sound orientation input
    first second receipt happly

private def iterationOperationalOpen
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Concrete.CheckedOpen  :=
  Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    (iterationInput input selection target)
    (iterationInput input selection target).plugLayout hadmissible boundary
    sourceRoot

private def iterationOperationalIso
    {input : Concrete.Checked }
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {receipt : OperationReceipt input}
    (realizes : receipt.Realizes
      (iterationInput input selection target).plugLayout.plugRaw
      (iterationWireProvenance input selection target)
      (iterationWireTransport input selection target))
    (hadmissible : (iterationInput input selection target).Admissible)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.OpenIso
      (iterationOperationalOpen input selection target hadmissible boundary
        sourceRoot).val
      (realizes.rawResultOpen mapped) := by
  let spliceInput := iterationInput input selection target
  let rawMapped := boundary.map fun wire =>
    spliceInput.plugLayout.frameWire (spliceInput.quotientWire wire)
  have expected : (iterationWireTransport input selection target
      ).transportBoundary boundary = some (realizes.targetBoundary mapped) :=
    realizes.transportBoundary_expected htransport
  have boundaryEq : realizes.targetBoundary mapped = rawMapped := by
    simpa [iterationWireTransport, spliceInput] using
      spliceFrameWireTransport_boundary_eq spliceInput boundary
        (realizes.targetBoundary mapped) expected
  apply realizes.operationalIso_to_rawResultOpen htransport rawMapped
  rw [← boundaryEq]
  exact expected

/-- Receipt bridge for the proper nested, nonempty iteration case. -/
private theorem applyIteration_sound_proper_nonempty
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyIteration input selection target = .ok receipt)
    (targetNe : target ≠ selection.val.anchor)
    (anchorNeRoot : selection.val.anchor ≠ input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyIteration_realizes happly
  have success := applyIteration_success input selection target receipt happly
  let hsplice := success.2.2
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _mapped _htransport =>
      iterationOperationalOpen input selection target hadmissible boundary
        sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      iterationOperationalIso realizes hadmissible boundary sourceRoot mapped
        htransport)
  intro model boundary sourceRoot mapped htransport args
  obtain ⟨certificate⟩ :=
    IterationSoundness.properIterationOpenAnchorContraction_complete input
      selection target hadmissible success.1 success.2.1 targetNe hnonempty
      boundary sourceRoot anchorNeRoot
  obtain ⟨alignment⟩ :=
    IterationSoundness.properIterationOpenTargetAlignment_complete certificate
  have semantic := IterationSoundness.properIterationOpen_output_equiv
    hsplice sourceRoot hnonempty certificate alignment model args
  cases orientation with
  | forward => simpa only [iterationOperationalOpen] using semantic.mp
  | backward => simpa only [iterationOperationalOpen] using semantic.mpr

/-- Receipt bridge for the proper nested, empty-spine iteration case. -/
private theorem applyIteration_sound_proper_zero
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyIteration input selection target = .ok receipt)
    (targetNe : target ≠ selection.val.anchor)
    (anchorNeRoot : selection.val.anchor ≠ input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyIteration_realizes happly
  have success := applyIteration_success input selection target receipt happly
  let hsplice := success.2.2
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _mapped _htransport =>
      iterationOperationalOpen input selection target hadmissible boundary
        sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      iterationOperationalIso realizes hadmissible boundary sourceRoot mapped
        htransport)
  intro model boundary sourceRoot mapped htransport args
  obtain ⟨certificate⟩ :=
    IterationSoundness.properIterationRootOpenAnchorContraction_complete input
      selection target hadmissible success.1 success.2.1 targetNe hzero
      boundary sourceRoot anchorNeRoot
  obtain ⟨alignment⟩ :=
    IterationSoundness.properIterationRootOpenTargetAlignment_complete
      certificate
  have semantic := IterationSoundness.properIterationRootOpen_output_equiv
    hsplice sourceRoot hzero certificate alignment model args
  cases orientation with
  | forward => simpa only [iterationOperationalOpen] using semantic.mp
  | backward => simpa only [iterationOperationalOpen] using semantic.mpr

/-- Receipt bridge for a proper root-anchor, nonempty-spine iteration. -/
private theorem applyIteration_sound_root_nonempty
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyIteration input selection target = .ok receipt)
    (targetNe : target ≠ selection.val.anchor)
    (hanchor : selection.val.anchor = input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyIteration_realizes happly
  have success := applyIteration_success input selection target receipt happly
  let hsplice := success.2.2
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _mapped _htransport =>
      iterationOperationalOpen input selection target hadmissible boundary
        sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      iterationOperationalIso realizes hadmissible boundary sourceRoot mapped
        htransport)
  intro model boundary sourceRoot mapped htransport args
  obtain ⟨closed⟩ :=
    IterationSoundness.properIterationAnchorContraction_complete input
      selection target hadmissible success.1 success.2.1 targetNe hnonempty
  obtain ⟨certificate⟩ :=
    IterationSoundness.properIterationRootAnchorItems_nonempty_complete input
      selection target hadmissible boundary sourceRoot hanchor targetNe
      hnonempty closed
  obtain ⟨alignment⟩ :=
    IterationSoundness.properIterationOrderedRootTargetAlignment_complete
      certificate
  have semantic :=
    IterationSoundness.properIterationOrderedRoot_output_equiv_nonempty
      hsplice sourceRoot hnonempty certificate alignment model args
  cases orientation with
  | forward => simpa only [iterationOperationalOpen] using semantic.mp
  | backward => simpa only [iterationOperationalOpen] using semantic.mpr

/-- Receipt bridge for a proper root-anchor, empty-spine iteration. -/
private theorem applyIteration_sound_root_zero
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyIteration input selection target = .ok receipt)
    (targetNe : target ≠ selection.val.anchor)
    (hanchor : selection.val.anchor = input.val.root)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount = 0) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyIteration_realizes happly
  have success := applyIteration_success input selection target receipt happly
  let hsplice := success.2.2
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _mapped _htransport =>
      iterationOperationalOpen input selection target hadmissible boundary
        sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      iterationOperationalIso realizes hadmissible boundary sourceRoot mapped
        htransport)
  intro model boundary sourceRoot mapped htransport args
  obtain ⟨closed⟩ :=
    IterationSoundness.properIterationRootAnchorContraction_complete input
      selection target hadmissible success.1 success.2.1 targetNe hzero
  obtain ⟨certificate⟩ :=
    IterationSoundness.properIterationRootAnchorItems_zero_complete input
      selection target hadmissible boundary sourceRoot hanchor targetNe closed
  obtain ⟨alignment⟩ :=
    IterationSoundness.properIterationOrderedRootTargetAlignment_complete
      certificate
  have semantic :=
    IterationSoundness.properIterationOrderedRoot_output_equiv_zero
      hsplice sourceRoot hzero certificate alignment model args
  cases orientation with
  | forward => simpa only [iterationOperationalOpen] using semantic.mp
  | backward => simpa only [iterationOperationalOpen] using semantic.mpr

/-- Receipt bridge for every executor-accepted same-site iteration. -/
private theorem applyIteration_sound_same
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyIteration input selection target = .ok receipt)
    (targetEq : target = selection.val.anchor) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyIteration_realizes happly
  have success := applyIteration_success input selection target receipt happly
  let hsplice := success.2.2
  let hadmissible := (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _mapped _htransport =>
      iterationOperationalOpen input selection target hadmissible boundary
        sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      iterationOperationalIso realizes hadmissible boundary sourceRoot mapped
        htransport)
  intro model boundary sourceRoot mapped htransport args
  by_cases hroot : target = input.val.root
  · by_cases hnonempty :
        (iterationInput input selection target).binderSpine.proxyCount ≠ 0
    · have semantic :=
        IterationSoundness.sameSite_root_output_equiv_nonempty hsplice
          sourceRoot targetEq success.2.1 hroot hnonempty model args
      cases orientation with
      | forward => simpa only [iterationOperationalOpen] using semantic.mp
      | backward => simpa only [iterationOperationalOpen] using semantic.mpr
    · have hzero :
          (iterationInput input selection target).binderSpine.proxyCount = 0 :=
        Nat.eq_zero_of_not_pos (fun positive =>
          hnonempty (Nat.ne_of_gt positive))
      have semantic := IterationSoundness.sameSite_root_output_equiv_zero
        hsplice sourceRoot targetEq success.2.1 hroot hzero
        model args
      cases orientation with
      | forward => simpa only [iterationOperationalOpen] using semantic.mp
      | backward => simpa only [iterationOperationalOpen] using semantic.mpr
  · by_cases hnonempty :
        (iterationInput input selection target).binderSpine.proxyCount ≠ 0
    · have semantic :=
        IterationSoundness.sameSite_nested_output_equiv_nonempty hsplice
          sourceRoot targetEq success.2.1 hroot hnonempty model args
      cases orientation with
      | forward => simpa only [iterationOperationalOpen] using semantic.mp
      | backward => simpa only [iterationOperationalOpen] using semantic.mpr
    · have hzero :
          (iterationInput input selection target).binderSpine.proxyCount = 0 :=
        Nat.eq_zero_of_not_pos (fun positive =>
          hnonempty (Nat.ne_of_gt positive))
      have semantic := IterationSoundness.sameSite_nested_output_equiv_zero
        hsplice sourceRoot targetEq success.2.1 hroot hzero
        model args
      cases orientation with
      | forward => simpa only [iterationOperationalOpen] using semantic.mp
      | backward => simpa only [iterationOperationalOpen] using semantic.mpr

/-- Every successful iteration receipt preserves ordered-open semantics. -/
theorem applyIteration_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyIteration input selection target = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  by_cases targetNe : target ≠ selection.val.anchor
  · by_cases anchorNeRoot : selection.val.anchor ≠ input.val.root
    · by_cases hnonempty :
        (iterationInput input selection target).binderSpine.proxyCount ≠ 0
      · exact applyIteration_sound_proper_nonempty orientation input
          selection target receipt happly targetNe anchorNeRoot hnonempty
      · have hzero :
            (iterationInput input selection target).binderSpine.proxyCount = 0 :=
          Nat.eq_zero_of_not_pos (fun positive =>
            hnonempty (Nat.ne_of_gt positive))
        exact applyIteration_sound_proper_zero orientation input
          selection target receipt happly targetNe anchorNeRoot hzero
    · have hanchor : selection.val.anchor = input.val.root := by
        exact Classical.byContradiction (fun distinct =>
          anchorNeRoot distinct)
      by_cases hnonempty :
          (iterationInput input selection target).binderSpine.proxyCount ≠ 0
      · exact applyIteration_sound_root_nonempty orientation input
          selection target receipt happly targetNe hanchor hnonempty
      · have hzero :
            (iterationInput input selection target).binderSpine.proxyCount = 0 :=
          Nat.eq_zero_of_not_pos (fun positive =>
            hnonempty (Nat.ne_of_gt positive))
        exact applyIteration_sound_root_zero orientation input
          selection target receipt happly targetNe hanchor hzero
  · have targetEq : target = selection.val.anchor := by
      exact Classical.byContradiction (fun distinct => targetNe distinct)
    exact applyIteration_sound_same orientation input selection target
      receipt happly targetEq

/-- The certified survivor occurrence can always be copied back into the
deiteration hole, and the operation-specific iteration theorem supplies its complete
ordered-open semantic equivalence for every anchor and binder-spine case. -/
private theorem deiterationReinsert_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (witness : OperationDeiterationWitness input selection) :
    SuccessfulReceiptSound orientation
      (IterationSoundness.deiterationRemoved input selection)
      (IterationSoundness.deiterationReinsertReceipt input selection
        witness) :=
  applyIteration_sound orientation
    (IterationSoundness.deiterationRemoved input selection)
    (IterationSoundness.deiterationRetainedSelection input selection witness)
    (IterationSoundness.deiterationReinsertTarget input selection)
    (IterationSoundness.deiterationReinsertReceipt input selection witness)
    (IterationSoundness.deiterationReinsertReceipt_spec input selection witness)

/-- Every successful deiteration receipt preserves ordered-open semantics. -/
theorem applyDeiteration_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (witness : OperationDeiterationWitness input selection)
    (receipt : OperationReceipt input)
    (happly : applyDeiteration input selection witness = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  exact IterationSoundness.deiteration_sound_of_reinsert orientation
    input selection witness receipt happly
    (deiterationReinsert_sound .forward input selection witness)
    (deiterationReinsert_sound .backward input selection witness)

/-- Every successful double-cut introduction receipt is equivalent. -/
theorem applyDoubleCutIntro_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (receipt : OperationReceipt input)
    (happly : applyDoubleCutIntro input selection = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyDoubleCutIntro_realizes happly
  have targetWellFormed :
      (doubleCutIntroRaw input.val selection).WellFormed  :=
    realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      ⟨ModalSoundness.doubleCutIntroRawOpen
          (OperationState.asCheckedOpen {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }).val selection,
        ModalSoundness.doubleCutIntroRawOpen_wellFormed
          (OperationState.asCheckedOpen {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }) selection targetWellFormed⟩)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      realizes.operationalIso_to_rawResultOpen htransport boundary
        (ModalSoundness.doubleCutIntroWireTransport_transportBoundary
          input.val selection boundary sourceRoot))
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target : Concrete.CheckedOpen  :=
    ⟨ModalSoundness.doubleCutIntroRawOpen source.asCheckedOpen.val selection,
      ModalSoundness.doubleCutIntroRawOpen_wellFormed source.asCheckedOpen
        selection targetWellFormed⟩
  let simulation := ModalSoundness.doubleCutIntroSimulation input selection
    targetWellFormed model
  have forward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model  simulation .forward
      (ModalSoundness.doubleCutIntroRootContext source.asCheckedOpen selection
        targetWellFormed model  .forward)
      True.intro args args
      (ModalSoundness.doubleCutIntroBoundaryWitness source.asCheckedOpen
        selection targetWellFormed .forward model  args)
  have backward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model  simulation .backward
      (ModalSoundness.doubleCutIntroRootContext source.asCheckedOpen selection
        targetWellFormed model  .backward)
      True.intro args args
      (ModalSoundness.doubleCutIntroBoundaryWitness source.asCheckedOpen
        selection targetWellFormed .backward model  args)
  dsimp only
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := forward sourceDenotes
      simpa [source, target] using targetDenotes
  | backward =>
      intro targetDenotes
      apply backward
      simpa [source, target] using targetDenotes

/-- Every successful double-cut elimination receipt is equivalent. -/
theorem applyDoubleCutElim_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (region : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyDoubleCutElim input region = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  obtain ⟨raw, hraw, realizes⟩ := applyDoubleCutElim_realizes happly
  let trace := doubleCutElimTrace hraw
  have rawWellFormed : raw.WellFormed  :=
    realizes.result_eq ▸ receipt.result.property
  have sourceWellFormed : trace.sourceDiagram.WellFormed  := by
    exact Eq.mp (congrArg (fun diagram => diagram.WellFormed )
      trace.promotion.raw_eq_diagram) rawWellFormed
  let rawBoundary := fun (boundary : List (Fin input.val.wireCount)) =>
    boundary.map (Fin.cast (doubleCutElimRaw?_wireCount hraw).symm)
  let operational := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (_mapped : List (Fin receipt.result.val.wireCount))
      (_htransport : receipt.interface.transportBoundary boundary =
        some _mapped) =>
    (⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed input.property boundary
        sourceRoot⟩ : Concrete.CheckedOpen )
  let operationalIso := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (mapped : List (Fin receipt.result.val.wireCount))
      (htransport : receipt.interface.transportBoundary boundary =
        some mapped) => by
    let rawOpen : Concrete.OpenDiagram := {
      diagram := raw
      boundary := rawBoundary boundary
    }
    let toRaw : Concrete.OpenIso (trace.sourceOpen boundary) rawOpen := {
      diagram := DoubleCutElimTrace.concreteIsoOfEq
        trace.promotion.raw_eq_diagram.symm
      boundary := by
        apply List.map_congr_left
        intro wire member
        apply Fin.ext
        exact DoubleCutElimTrace.concreteIsoOfEq_wires_val
          trace.promotion.raw_eq_diagram.symm wire
    }
    exact toRaw.trans
      (realizes.operationalIso_to_rawResultOpen htransport
        (rawBoundary boundary)
        (DoubleCutElimTrace.interfaceTransport_transportBoundary hraw
          input.property boundary sourceRoot))
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := operational) (operationalIso := operationalIso)
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target : Concrete.CheckedOpen  :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed input.property boundary
        sourceRoot⟩
  let original : Concrete.CheckedOpen  :=
    ⟨DoubleCutElimTrace.targetOpen input.val boundary,
      DoubleCutElimTrace.targetOpen_wellFormed input.property boundary
        sourceRoot⟩
  let simulation := trace.semanticSimulation sourceWellFormed input.property
    model
  have forward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      target original model  simulation .forward
      (trace.rootContextSimulation sourceWellFormed input.property boundary
        sourceRoot model  .forward)
      True.intro args args
      (trace.boundaryWitness sourceWellFormed input.property boundary
        sourceRoot .forward model  args)
  have backward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      target original model  simulation .backward
      (trace.rootContextSimulation sourceWellFormed input.property boundary
        sourceRoot model  .backward)
      True.intro args args
      (trace.boundaryWitness sourceWellFormed input.property boundary
        sourceRoot .backward model  args)
  dsimp only
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := backward sourceDenotes
      simpa [source, target, original, operational] using targetDenotes
  | backward =>
      intro targetDenotes
      apply forward
      simpa [source, target, original, operational] using targetDenotes

/-- Every successful vacuous-cut introduction receipt is equivalent. -/
theorem applyVacuousIntro_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) (arity : Nat)
    (receipt : OperationReceipt input)
    (happly : applyVacuousIntro input selection arity = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyVacuousIntro_realizes happly
  have targetWellFormed :
      (vacuousIntroRaw input.val selection arity).WellFormed  :=
    realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      ⟨VacuousSoundness.vacuousIntroRawOpen
          (OperationState.asCheckedOpen {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }).val selection arity,
        VacuousSoundness.vacuousIntroRawOpen_wellFormed
          (OperationState.asCheckedOpen {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }) selection arity targetWellFormed⟩)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      realizes.operationalIso_to_rawResultOpen htransport boundary
        (VacuousSoundness.vacuousIntroWireTransport_transportBoundary
          input.val selection arity boundary sourceRoot))
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target : Concrete.CheckedOpen  :=
    ⟨VacuousSoundness.vacuousIntroRawOpen source.asCheckedOpen.val selection
        arity,
      VacuousSoundness.vacuousIntroRawOpen_wellFormed source.asCheckedOpen
        selection arity targetWellFormed⟩
  let simulation := VacuousSoundness.vacuousIntroSimulation input selection
    arity targetWellFormed model
  have forward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model  simulation .forward
      (VacuousSoundness.vacuousIntroRootContext source.asCheckedOpen selection
        arity targetWellFormed model  .forward)
      True.intro args args
      (VacuousSoundness.vacuousIntroBoundaryWitness source.asCheckedOpen
        selection arity targetWellFormed .forward model  args)
  have backward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model  simulation .backward
      (VacuousSoundness.vacuousIntroRootContext source.asCheckedOpen selection
        arity targetWellFormed model  .backward)
      True.intro args args
      (VacuousSoundness.vacuousIntroBoundaryWitness source.asCheckedOpen
        selection arity targetWellFormed .backward model  args)
  dsimp only
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := forward sourceDenotes
      simpa [source, target] using targetDenotes
  | backward =>
      intro targetDenotes
      apply backward
      simpa [source, target] using targetDenotes

/-- Every successful vacuous-cut elimination receipt is equivalent. -/
theorem applyVacuousElim_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (region : Fin input.val.regionCount)
    (receipt : OperationReceipt input)
    (happly : applyVacuousElim input region = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  obtain ⟨raw, hraw, realizes⟩ := applyVacuousElim_realizes happly
  let trace := vacuousElimTrace hraw
  have rawWellFormed : raw.WellFormed  :=
    realizes.result_eq ▸ receipt.result.property
  have sourceWellFormed : trace.sourceDiagram.WellFormed  := by
    exact Eq.mp (congrArg (fun diagram => diagram.WellFormed )
      trace.promotion.raw_eq_diagram) rawWellFormed
  let rawBoundary := fun (boundary : List (Fin input.val.wireCount)) =>
    boundary.map (Fin.cast (vacuousElimRaw?_wireCount hraw).symm)
  let operational := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (_mapped : List (Fin receipt.result.val.wireCount))
      (_htransport : receipt.interface.transportBoundary boundary =
        some _mapped) =>
    (⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed input.property boundary
        sourceRoot⟩ : Concrete.CheckedOpen )
  let operationalIso := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (mapped : List (Fin receipt.result.val.wireCount))
      (htransport : receipt.interface.transportBoundary boundary =
        some mapped) => by
    let rawOpen : Concrete.OpenDiagram := {
      diagram := raw
      boundary := rawBoundary boundary
    }
    let toRaw : Concrete.OpenIso (trace.sourceOpen boundary) rawOpen := {
      diagram := VacuousElimTrace.concreteIsoOfEq
        trace.promotion.raw_eq_diagram.symm
      boundary := by
        apply List.map_congr_left
        intro wire member
        apply Fin.ext
        exact VacuousElimTrace.concreteIsoOfEq_wires_val
          trace.promotion.raw_eq_diagram.symm wire
    }
    exact toRaw.trans
      (realizes.operationalIso_to_rawResultOpen htransport
        (rawBoundary boundary)
        (VacuousElimTrace.interfaceTransport_transportBoundary hraw
          input.property boundary sourceRoot))
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := operational) (operationalIso := operationalIso)
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target : Concrete.CheckedOpen  :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed input.property boundary
        sourceRoot⟩
  let original : Concrete.CheckedOpen  :=
    ⟨VacuousElimTrace.targetOpen input.val boundary,
      VacuousElimTrace.targetOpen_wellFormed input.property boundary
        sourceRoot⟩
  let freshForward := fun {sourceRels targetRels : RelCtx}
      (_sourceContext : Concrete.Elaboration.WireContext trace.sourceDiagram)
      (_targetContext : Concrete.Elaboration.WireContext input.val)
      (_sourceBinders : Concrete.Elaboration.BinderContext
        trace.sourceDiagram sourceRels)
      (_targetBinders : Concrete.Elaboration.BinderContext input.val targetRels)
      (_sourceExact : _sourceContext.Exact
        (trace.targetIndex input.property))
      (_targetExact : (_targetContext.extend region).Exact region)
      (_sourceCover : _sourceBinders.Covers
        (trace.targetIndex input.property))
      (_targetCover : _targetBinders.Covers trace.parent)
      (_sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
        trace.sourceDiagram _sourceBinders
          (trace.targetIndex input.property))
      (_targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
        input.val _targetBinders trace.parent)
      (_binderWitness : VacuousElimTrace.MappedBinderWitness trace
        _sourceBinders _targetBinders)
      (_sourceEnvironment : Fin _sourceContext.length → model.Carrier)
      (_targetEnvironment : Fin _targetContext.length → model.Carrier)
      (_sourceRelations : RelEnv model.Carrier sourceRels)
      (_targetRelations : RelEnv model.Carrier targetRels) =>
    (fun _ => False : Relation model.Carrier trace.arity)
  let simulation := trace.semanticSimulation sourceWellFormed input.property
    model  freshForward
  have forward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      target original model  simulation .forward
      (trace.rootContextSimulation sourceWellFormed input.property boundary
        sourceRoot model  freshForward .forward)
      True.intro args args
      (trace.boundaryWitness sourceWellFormed input.property boundary
        sourceRoot .forward model  freshForward args)
  have backward :=
    Concrete.Elaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      target original model  simulation .backward
      (trace.rootContextSimulation sourceWellFormed input.property boundary
        sourceRoot model  freshForward .backward)
      True.intro args args
      (trace.boundaryWitness sourceWellFormed input.property boundary
        sourceRoot .backward model  freshForward args)
  dsimp only
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := backward sourceDenotes
      simpa [source, target, original, operational] using targetDenotes
  | backward =>
      intro targetDenotes
      apply forward
      simpa [source, target, original, operational] using targetDenotes


end VisualProof.Rule
