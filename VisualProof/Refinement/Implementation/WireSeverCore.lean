import VisualProof.Concrete.Step

namespace VisualProof.Refinement.Implementation.WireSever

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

theorem allFin_succ_last_soundness (n : Nat) :
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

theorem listGet_cast_of_eq {left right : List α}
    (equality : left = right) (index : Fin left.length) :
    left.get index = right.get (Fin.cast (congrArg List.length equality) index) := by
  subst right
  rfl

theorem listGet_map_cast_soundness (values : List α) (f : α → β)
    (index : Fin values.length) :
    (values.map f).get
        (Fin.cast (List.length_map (as := values) f).symm index) =
      f (values.get index) := by
  simpa only [List.get_eq_getElem, Fin.val_cast] using
    (List.getElem_map (l := values) (i := index.val) f)
@[simp] theorem severWireRaw_regionCount
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).regionCount = input.regionCount :=
  rfl

@[simp] theorem severWireRaw_nodeCount
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).nodeCount = input.nodeCount :=
  rfl

@[simp] theorem severWireRaw_root
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).root = input.root :=
  rfl

@[simp] theorem severWireRaw_regions
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount) :
    (severWireRaw input wire keep).regions region = input.regions region :=
  rfl

@[simp] theorem severWireRaw_nodes
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (node : Fin input.nodeCount) :
    (severWireRaw input wire keep).nodes node = input.nodes node :=
  rfl

@[simp] theorem severWireRaw_oldWire
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).wires candidate.castSucc =
      if candidate = wire then
        { scope := (input.wires wire).scope
          endpoints := (input.wires wire).endpoints.filter
            (fun endpoint => decide (endpoint ∈ keep)) }
      else input.wires candidate := by
  simp [severWireRaw]

@[simp] theorem severWireRaw_freshWire
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    (severWireRaw input wire keep).wires (Fin.last input.wireCount) =
      { scope := (input.wires wire).scope
        endpoints := (input.wires wire).endpoints.filter
          (fun endpoint => decide (endpoint ∉ keep)) } := by
  simp [severWireRaw]

theorem severWireRaw_oldWire_scope
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    ((severWireRaw input wire keep).wires candidate.castSucc).scope =
      (input.wires candidate).scope := by
  by_cases hcandidate : candidate = wire
  · subst candidate
    simp
  · simp [hcandidate]

theorem severWireRaw_freshWire_scope
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    ((severWireRaw input wire keep).wires
      (Fin.last input.wireCount)).scope = (input.wires wire).scope := by
  simp

theorem severWireRaw_exactScopeWires
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

theorem severWireRaw_exactScopeWires_of_ne
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount))
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope) :
    Concrete.Elaboration.exactScopeWires (severWireRaw input wire keep) region =
      (Concrete.Elaboration.exactScopeWires input region).map Fin.castSucc := by
  rw [severWireRaw_exactScopeWires]
  simp [hne]

theorem severWireRaw_exactScopeWires_length_of_ne
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

def severWireCollapse (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    Fin (severWireRaw input wire keep).wireCount → Fin input.wireCount :=
  Fin.lastCases wire id

@[simp] theorem severWireCollapse_old
    (input : Concrete.Diagram) (wire candidate : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    severWireCollapse input wire keep candidate.castSucc =
      candidate := by
  simp [severWireCollapse]

@[simp] theorem severWireCollapse_fresh
    (input : Concrete.Diagram) (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    severWireCollapse input wire keep (Fin.last input.wireCount) =
      wire := by
  simp [severWireCollapse]

theorem severWireRaw_endpointOccurs_collapse
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

theorem severWireRaw_endpointOccurs_lift
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

structure SeverContextCollapse
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

noncomputable def ofMem
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

theorem severWireRaw_scope_collapse
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

theorem severWireRaw_exactScopeWires_mem_collapse
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

noncomputable def SeverContextCollapse.extend
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

theorem SeverContextCollapse.extend_index_inherited
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

theorem SeverContextCollapse.extend_index_local_of_ne
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

theorem severWireRaw_resolvePort?_collapse
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

theorem severWireRaw_compileNode?_collapse
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
@[simp] theorem severWireRaw_localOccurrences
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

def severWireRawOpen (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    Concrete.OpenDiagram where
  diagram := severWireRaw source.diagram wire keep
  boundary := source.boundary.map Fin.castSucc

theorem severWireRawOpen_exposedWires
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

theorem severWireRawOpen_wellFormed
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

theorem severWireRawOpen_hiddenWires
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

theorem severWireRawOpen_rootWires
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
noncomputable def severWireRawOpen_rootCollapse
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

theorem severWireRawOpen_rootCollapse_source_nodup
    (source : Concrete.CheckedOpen ) :
    source.val.rootWires.Nodup :=
  source.val.rootWires_nodup

def severExposedIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (keep : List (CEndpoint source.diagram.nodeCount)) :
    Fin (severWireRawOpen source wire keep).exposedWires.length →
      Fin source.exposedWires.length :=
  Fin.cast (by
    exact (congrArg List.length
      (severWireRawOpen_exposedWires source wire keep)).trans
        (List.length_map (as := source.exposedWires) Fin.castSucc))

theorem severExposedIndex_get
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

noncomputable def severHiddenIndex
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

theorem severHiddenIndex_get
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

theorem severRootCollapse_index_exposed
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

theorem severRootCollapse_index_hidden_of_ne
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
theorem severBoundaryLengthEq
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

theorem severBoundaryClass
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
end VisualProof.Refinement.Implementation.WireSever
