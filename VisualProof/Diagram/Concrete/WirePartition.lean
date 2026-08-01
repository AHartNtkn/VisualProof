import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval

namespace VisualProof

namespace ConcreteWireQuantifier

private def wireSeverCandidate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (scope : source.val.RegionId) :
    ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount
  wireCount := source.val.wireCount + 1
  root := source.val.root
  regions := source.val.regions
  nodes := source.val.nodes
  wires :=
    Fin.addCases
      (fun candidate =>
        let data := source.val.wires candidate
        if candidate = wire then
          { data with
            endpoints := data.endpoints.filter fun endpoint =>
              decide (endpoint ∈ keep) }
        else
          data)
      (fun _ =>
        let data := source.val.wires wire
        { data with
          scope := scope
          endpoints := data.endpoints.filter fun endpoint =>
            decide (endpoint ∉ keep) })

private def wireJoinWires
    (source : CheckedDiagram definitions)
    (inner : source.val.WireId) :
    List source.val.WireId :=
  source.val.wiresList.filter fun candidate =>
    decide (candidate ≠ inner)

private theorem filter_ne_length_of_nodup_mem
    [DecidableEq α] {removed : α} {values : List α}
    (nodup : values.Nodup) (member : removed ∈ values) :
    (values.filter fun value => decide (value ≠ removed)).length =
      values.length - 1 := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      rcases nodup with ⟨headFresh, tailNodup⟩
      by_cases same : head = removed
      · subst head
        have retained :
            tail.filter (fun value => decide (value ≠ removed)) = tail :=
          List.filter_eq_self.mpr fun value valueMember => by
            apply decide_eq_true
            intro equality
            subst value
            exact headFresh valueMember
        rw [List.filter_cons_of_neg (by simp), retained]
        simp
      · have tailMember : removed ∈ tail := by
          rcases List.mem_cons.mp member with equality | tailMember
          · exact False.elim (same equality.symm)
          · exact tailMember
        rw [List.filter_cons_of_pos (by simp [same])]
        simp only [List.length_cons]
        have tailLength := induction tailNodup tailMember
        have tailPositive : 0 < tail.length :=
          List.length_pos_iff.mpr (by
            intro empty
            subst tail
            simp at tailMember)
        omega

private def wireJoinCandidate
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) :
    ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount
  wireCount := (wireJoinWires source inner).length
  root := source.val.root
  regions := source.val.regions
  nodes := source.val.nodes
  wires := fun target =>
    let sourceWire := (wireJoinWires source inner).get target
    let data := source.val.wires sourceWire
    if sourceWire = outer then
      { data with
        endpoints :=
          data.endpoints ++ (source.val.wires inner).endpoints }
    else
      data

/-- Checked output of one individual-wire endpoint partition. -/
structure WireSeverResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (scope : source.val.RegionId) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private scopeInside :
    source.val.Encloses (source.val.wires wire).scope scope
  private generated :
    checked.val = wireSeverCandidate source wire keep scope
  private rejoined : CheckedDiagram definitions
  private rejoinedGenerated :
    rejoined.val =
      wireJoinCandidate checked
        (Internal.checkedWire generated (Fin.castAdd 1 wire))
        (Internal.checkedWire generated
          (Fin.natAdd source.val.wireCount (0 : Fin 1)))

namespace WireSeverResult

def regionImage
    (result : WireSeverResult source wire keep scope)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated region

def nodeImage
    (result : WireSeverResult source wire keep scope)
    (node : source.val.NodeId) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated node

def wireImage
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated (Fin.castAdd 1 sourceWire)

def freshWire
    (result : WireSeverResult source wire keep scope) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.natAdd source.val.wireCount (0 : Fin 1))

def endpointImage
    (result : WireSeverResult source wire keep scope)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.checked.val.nodeCount :=
  Internal.checkedEndpoint result.generated endpoint

def renameRegion
    (result : WireSeverResult source wire keep scope) :
    CRegion source.val.regionCount →
      CRegion result.checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (result.regionImage parent)

def renameNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    {scope : source.val.RegionId}
    (result : WireSeverResult source wire keep scope) :
    CNode source.val.regionCount definitions.length →
      CNode result.checked.val.regionCount definitions.length
  | .atom region args => .atom (result.regionImage region) args
  | .ref region definition args =>
      .ref (result.regionImage region) definition args
  | .identity region sig arity =>
      .identity (result.regionImage region) sig arity

theorem checked_generated
    (result : WireSeverResult source wire keep scope) :
    result.checked.val = wireSeverCandidate source wire keep scope :=
  result.generated

@[simp] theorem regionCount
    (result : WireSeverResult source wire keep scope) :
    result.checked.val.regionCount = source.val.regionCount :=
  by
    simpa [wireSeverCandidate] using
      congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : WireSeverResult source wire keep scope) :
    result.checked.val.nodeCount = source.val.nodeCount :=
  by
    simpa [wireSeverCandidate] using
      congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : WireSeverResult source wire keep scope) :
    result.checked.val.wireCount = source.val.wireCount + 1 :=
  by
    simpa [wireSeverCandidate] using
      congrArg ConcreteDiagram.wireCount result.generated

@[simp] theorem root_generated
    (result : WireSeverResult source wire keep scope) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  rw [Internal.checkedRoot_transport]
  rfl

@[simp] theorem region_generated
    (result : WireSeverResult source wire keep scope)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionImage region) =
      result.renameRegion (source.val.regions region) := by
  unfold regionImage renameRegion
  rw [Internal.checkedRegion_data_transport]
  simp only [wireSeverCandidate]
  cases source.val.regions region <;> rfl

theorem climb_regionImage
    (result : WireSeverResult source wire keep scope)
    (steps : Nat) (region : source.val.RegionId) :
    result.checked.val.climb steps (result.regionImage region) =
      (source.val.climb steps region).map result.regionImage := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      simp only [ConcreteDiagram.climb]
      rw [result.region_generated]
      cases data : source.val.regions region with
      | sheet => rfl
      | cut parent =>
          simp only [WireSeverResult.renameRegion]
          exact induction parent

/-- Source enclosure is preserved by the partition's region embedding. -/
theorem encloses_regionImage
    (result : WireSeverResult source wire keep scope)
    {ancestor descendant : source.val.RegionId}
    (encloses : source.val.Encloses ancestor descendant) :
    result.checked.val.Encloses
      (result.regionImage ancestor) (result.regionImage descendant) := by
  unfold ConcreteDiagram.Encloses at encloses ⊢
  rw [List.any_eq_true] at encloses ⊢
  obtain ⟨steps, _, climbed⟩ := encloses
  let targetSteps : Fin (result.checked.val.regionCount + 1) :=
    Fin.cast
      (congrArg (fun count => count + 1) result.regionCount.symm)
      steps
  refine ⟨targetSteps, Data.Finite.mem_allFin targetSteps, ?_⟩
  change
    (result.checked.val.climb steps.val
      (result.regionImage descendant) ==
        some (result.regionImage ancestor)) = true
  rw [result.climb_regionImage, eq_of_beq climbed]
  simp

@[simp] theorem node_generated
    (result : WireSeverResult source wire keep scope)
    (node : source.val.NodeId) :
    result.checked.val.nodes (result.nodeImage node) =
      result.renameNode (source.val.nodes node) := by
  unfold nodeImage renameNode
  rw [Internal.checkedNode_data_transport]
  simp only [wireSeverCandidate]
  cases source.val.nodes node <;> rfl

@[simp] theorem wireImage_signature
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  unfold wireImage
  rw [Internal.checkedWire_signature_transport]
  simp [wireSeverCandidate]
  split <;> rfl

@[simp] theorem freshWire_signature
    (result : WireSeverResult source wire keep scope) :
    (result.checked.val.wires result.freshWire).sig =
      (source.val.wires wire).sig := by
  unfold freshWire
  rw [Internal.checkedWire_signature_transport]
  simp only [wireSeverCandidate, Fin.addCases_right]

@[simp] theorem wireImage_scope
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold wireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  simp [wireSeverCandidate]
  split <;> rfl

@[simp] theorem freshWire_scope
    (result : WireSeverResult source wire keep scope) :
    (result.checked.val.wires result.freshWire).scope =
      result.regionImage scope := by
  unfold freshWire regionImage
  rw [Internal.checkedWire_scope_transport]
  simp only [wireSeverCandidate, Fin.addCases_right]

theorem wireImage_endpoints
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).endpoints =
      (if sourceWire = wire then
        (source.val.wires sourceWire).endpoints.filter fun endpoint =>
          decide (endpoint ∈ keep)
      else
        (source.val.wires sourceWire).endpoints).map result.endpointImage := by
  unfold wireImage endpointImage
  rw [Internal.checkedWire_endpoints_transport]
  simp only [wireSeverCandidate, Fin.addCases_left]
  split <;> rfl

theorem freshWire_endpoints
    (result : WireSeverResult source wire keep scope) :
    (result.checked.val.wires result.freshWire).endpoints =
      ((source.val.wires wire).endpoints.filter fun endpoint =>
        decide (endpoint ∉ keep)).map result.endpointImage := by
  unfold freshWire endpointImage
  rw [Internal.checkedWire_endpoints_transport]
  simp only [wireSeverCandidate, Fin.addCases_right]

/-- The chosen fresh-wire scope lies inside the original wire scope. -/
theorem sourceScope_encloses_scope
    (result : WireSeverResult source wire keep scope) :
    source.val.Encloses (source.val.wires wire).scope scope :=
  result.scopeInside

end WireSeverResult

/--
Split one wire by an exact endpoint partition. The new wire uses the chosen
scope, which must lie inside the old scope; polarity remains rule-owned.
-/
def severWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (scope : source.val.RegionId) :
    Except Error (WireSeverResult source wire keep scope) := by
  if partition :
        ∀ endpoint, endpoint ∈ keep →
          endpoint ∈ (source.val.wires wire).endpoints then
    if scopeInside :
        source.val.Encloses (source.val.wires wire).scope scope then
      let candidate := wireSeverCandidate source wire keep scope
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          let generated :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          let retained :=
            Internal.checkedWire generated (Fin.castAdd 1 wire)
          let fresh :=
            Internal.checkedWire generated
              (Fin.natAdd source.val.wireCount (0 : Fin 1))
          let rejoinCandidate :=
            wireJoinCandidate checked retained fresh
          match rejoinAccepted :
              ConcreteDiagram.checkWellFormed definitions rejoinCandidate with
          | .error error =>
              exact .error (.wellFormed error)
          | .ok rejoined =>
              exact .ok
                (WireSeverResult.mk checked scopeInside generated rejoined
                  (ConcreteDiagram.checkWellFormed_preserves_input
                    rejoinAccepted))
    else
      exact .error .invalidSeverScope
  else
    exact .error .invalidEndpointPartition

/-- Checked output of one comparable-scope individual-wire merge. -/
structure WireJoinResult
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private different : outer ≠ inner
  private signaturesEqual :
    (source.val.wires outer).sig = (source.val.wires inner).sig
  private generated :
    checked.val = wireJoinCandidate source outer inner

namespace WireJoinResult

def regionImage
    (result : WireJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated region

def nodeImage
    (result : WireJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated node

def wireImage
    (result : WireJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (DenseList.index (wireJoinWires source inner) sourceWire (by
      simp [wireJoinWires, ConcreteDiagram.wiresList,
        Data.Finite.mem_allFin, survives]))

def outerWire
    (result : WireJoinResult source outer inner) :
    result.checked.val.WireId :=
  result.wireImage outer result.different

def endpointImage
    (result : WireJoinResult source outer inner)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.checked.val.nodeCount :=
  Internal.checkedEndpoint result.generated endpoint

def renameRegion
    (result : WireJoinResult source outer inner) :
    CRegion source.val.regionCount →
      CRegion result.checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (result.regionImage parent)

def renameNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : WireJoinResult source outer inner) :
    CNode source.val.regionCount definitions.length →
      CNode result.checked.val.regionCount definitions.length
  | .atom region args => .atom (result.regionImage region) args
  | .ref region definition args =>
      .ref (result.regionImage region) definition args
  | .identity region sig arity =>
      .identity (result.regionImage region) sig arity

theorem checked_generated
    (result : WireJoinResult source outer inner) :
    result.checked.val = wireJoinCandidate source outer inner :=
  result.generated

theorem outer_ne_inner
    (result : WireJoinResult source outer inner) :
    outer ≠ inner :=
  result.different

@[simp] theorem source_signatures_equal
    (result : WireJoinResult source outer inner) :
    (source.val.wires outer).sig = (source.val.wires inner).sig :=
  result.signaturesEqual

@[simp] theorem regionCount
    (result : WireJoinResult source outer inner) :
    result.checked.val.regionCount = source.val.regionCount := by
  simpa [wireJoinCandidate] using
    congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : WireJoinResult source outer inner) :
    result.checked.val.nodeCount = source.val.nodeCount := by
  simpa [wireJoinCandidate] using
    congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : WireJoinResult source outer inner) :
    result.checked.val.wireCount = (wireJoinWires source inner).length := by
  simpa [wireJoinCandidate] using
    congrArg ConcreteDiagram.wireCount result.generated

@[simp] theorem wireCount_succ
    (result : WireJoinResult source outer inner) :
    result.checked.val.wireCount + 1 = source.val.wireCount := by
  rw [result.wireCount]
  unfold wireJoinWires
  unfold ConcreteDiagram.wiresList
  rw [filter_ne_length_of_nodup_mem
    (Data.Finite.allFin_nodup source.val.wireCount)
    (Data.Finite.mem_allFin inner)]
  simp only [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange,
    List.length_finRange]
  have bound := inner.isLt
  have positive : 0 < source.val.wireCount := by omega
  omega

/-- The exact pre-join wire represented by one dense target identifier. -/
def sourceWire
    (result : WireJoinResult source outer inner)
    (target : result.checked.val.WireId) : source.val.WireId :=
  (wireJoinWires source inner).get
    (Fin.cast result.wireCount target)

theorem sourceWire_ne_inner
    (result : WireJoinResult source outer inner)
    (target : result.checked.val.WireId) :
    result.sourceWire target ≠ inner := by
  have member : result.sourceWire target ∈ wireJoinWires source inner :=
    List.get_mem _ _
  exact of_decide_eq_true (List.mem_filter.mp member).2

@[simp] theorem sourceWire_wireImage
    (result : WireJoinResult source outer inner)
    (source : source.val.WireId)
    (survives : source ≠ inner) :
    result.sourceWire (result.wireImage source survives) = source := by
  unfold sourceWire wireImage
  have member : source ∈ wireJoinWires _ inner := by
    simp [wireJoinWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  apply Fin.ext
  change
    ((wireJoinWires _ inner).get
      (DenseList.index (wireJoinWires _ inner) source member)).val =
      source.val
  rw [DenseList.get_index]

@[simp] theorem wireImage_sourceWire
    (result : WireJoinResult source outer inner)
    (target : result.checked.val.WireId) :
    result.wireImage (result.sourceWire target)
        (result.sourceWire_ne_inner target) = target := by
  unfold sourceWire wireImage
  apply Fin.ext
  change
    (DenseList.index (wireJoinWires source inner)
      ((wireJoinWires source inner).get
        (Fin.cast result.wireCount target)) _).val = target.val
  rw [DenseList.index_get (wireJoinWires source inner)
    ((Data.Finite.allFin_nodup source.val.wireCount).filter _)
    (Fin.cast result.wireCount target)]
  rfl

@[simp] theorem root_generated
    (result : WireJoinResult source outer inner) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  rw [Internal.checkedRoot_transport]
  rfl

@[simp] theorem region_generated
    (result : WireJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionImage region) =
      result.renameRegion (source.val.regions region) := by
  unfold regionImage renameRegion
  rw [Internal.checkedRegion_data_transport]
  simp only [wireJoinCandidate]
  cases source.val.regions region <;> rfl

@[simp] theorem node_generated
    (result : WireJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.checked.val.nodes (result.nodeImage node) =
      result.renameNode (source.val.nodes node) := by
  unfold nodeImage renameNode
  rw [Internal.checkedNode_data_transport]
  simp only [wireJoinCandidate]
  cases source.val.nodes node <;> rfl

@[simp] theorem wireImage_signature
    (result : WireJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).sig =
      (source.val.wires sourceWire).sig := by
  unfold wireImage
  rw [Internal.checkedWire_signature_transport]
  simp only [wireJoinCandidate]
  rw [DenseList.get_index]
  split <;> rfl

@[simp] theorem wireImage_scope
    (result : WireJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold wireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  simp only [wireJoinCandidate]
  rw [DenseList.get_index]
  split <;> rfl

theorem wireImage_endpoints
    (result : WireJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).endpoints =
      (if sourceWire = outer then
        (source.val.wires outer).endpoints ++
          (source.val.wires inner).endpoints
      else
        (source.val.wires sourceWire).endpoints).map
          result.endpointImage := by
  unfold wireImage endpointImage
  rw [Internal.checkedWire_endpoints_transport]
  simp only [wireJoinCandidate]
  rw [DenseList.get_index]
  split
  · rename_i same
    subst sourceWire
    rfl
  · rfl

end WireJoinResult

namespace WireSeverResult

/--
The checker-owned inverse join of an accepted wire sever. Its checked target
is the canonical stable-partition rejoin retained by the sever receipt.
-/
def inverseJoin
    (result : WireSeverResult source wire keep scope) :
    WireJoinResult result.checked (result.wireImage wire)
      result.freshWire :=
  WireJoinResult.mk result.rejoined (by
    intro same
    have values := congrArg Fin.val same
    unfold wireImage freshWire Internal.checkedWire at values
    simp only [Fin.coe_cast, Fin.val_castAdd, Fin.val_natAdd] at values
    omega)
    (by
      rw [result.wireImage_signature, result.freshWire_signature])
    (by
      simpa [wireImage, freshWire] using result.rejoinedGenerated)

@[simp] theorem inverseJoin_checked
    (result : WireSeverResult source wire keep scope) :
    result.inverseJoin.checked = result.rejoined :=
  rfl

@[simp] theorem inverseJoin_regionCount
    (result : WireSeverResult source wire keep scope) :
    result.inverseJoin.checked.val.regionCount = source.val.regionCount := by
  rw [result.inverseJoin.regionCount, result.regionCount]

@[simp] theorem inverseJoin_nodeCount
    (result : WireSeverResult source wire keep scope) :
    result.inverseJoin.checked.val.nodeCount = source.val.nodeCount := by
  rw [result.inverseJoin.nodeCount, result.nodeCount]

@[simp] theorem inverseJoin_wireCount
    (result : WireSeverResult source wire keep scope) :
    result.inverseJoin.checked.val.wireCount = source.val.wireCount := by
  rw [result.inverseJoin.wireCount]
  unfold wireJoinWires
  unfold ConcreteDiagram.wiresList
  rw [filter_ne_length_of_nodup_mem
    (Data.Finite.allFin_nodup result.checked.val.wireCount)
    (Data.Finite.mem_allFin result.freshWire)]
  simp only [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange,
    List.length_finRange]
  rw [result.wireCount]
  omega

private def inverseRegion
    (result : WireSeverResult source wire keep scope)
    (region : source.val.RegionId) :
    result.inverseJoin.checked.val.RegionId :=
  Fin.cast result.inverseJoin_regionCount.symm region

private def inverseNode
    (result : WireSeverResult source wire keep scope)
    (node : source.val.NodeId) :
    result.inverseJoin.checked.val.NodeId :=
  Fin.cast result.inverseJoin_nodeCount.symm node

@[simp] private theorem inverse_regionImage
    (result : WireSeverResult source wire keep scope)
    (region : source.val.RegionId) :
    result.inverseJoin.regionImage (result.regionImage region) =
      result.inverseRegion region := by
  apply Fin.ext
  rfl

@[simp] private theorem inverse_nodeImage
    (result : WireSeverResult source wire keep scope)
    (node : source.val.NodeId) :
    result.inverseJoin.nodeImage (result.nodeImage node) =
      result.inverseNode node := by
  apply Fin.ext
  rfl

theorem retained_ne_fresh
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    result.wireImage sourceWire ≠ result.freshWire := by
  intro same
  have values := congrArg Fin.val same
  unfold wireImage freshWire Internal.checkedWire at values
  simp only [Fin.coe_cast, Fin.val_castAdd, Fin.val_natAdd] at values
  omega

private def rejoinSourceWire
    (result : WireSeverResult source wire keep scope)
    (target : result.inverseJoin.checked.val.WireId) :
    result.checked.val.WireId :=
  (wireJoinWires result.checked result.freshWire).get
    (Fin.cast result.inverseJoin.wireCount target)

private theorem rejoinSourceWire_survives
    (result : WireSeverResult source wire keep scope)
    (target : result.inverseJoin.checked.val.WireId) :
    result.rejoinSourceWire target ≠ result.freshWire := by
  have member :
      result.rejoinSourceWire target ∈
        wireJoinWires result.checked result.freshWire :=
    List.get_mem _ _
  exact of_decide_eq_true (List.mem_filter.mp member).2

@[simp] private theorem inverseJoin_wireImage_sourceWire
    (result : WireSeverResult source wire keep scope)
    (target : result.inverseJoin.checked.val.WireId) :
    result.inverseJoin.wireImage (result.rejoinSourceWire target)
        (result.rejoinSourceWire_survives target) =
      target := by
  unfold WireJoinResult.wireImage rejoinSourceWire
  apply Fin.ext
  change
    (DenseList.index
      (wireJoinWires result.checked result.freshWire)
      ((wireJoinWires result.checked result.freshWire).get
        (Fin.cast result.inverseJoin.wireCount target)) _).val =
      target.val
  rw [DenseList.index_get
    (wireJoinWires result.checked result.freshWire)
    ((Data.Finite.allFin_nodup result.checked.val.wireCount).filter _)
    (Fin.cast result.inverseJoin.wireCount target)]
  rfl

@[simp] private theorem rejoinSourceWire_wireImage
    (result : WireSeverResult source wire keep scope)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    result.rejoinSourceWire
        (result.inverseJoin.wireImage splitWire survives) =
      splitWire := by
  have member :
      splitWire ∈ wireJoinWires result.checked result.freshWire := by
    simp [wireJoinWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  unfold rejoinSourceWire WireJoinResult.wireImage
  apply Fin.ext
  change
    ((wireJoinWires result.checked result.freshWire).get
      (DenseList.index
        (wireJoinWires result.checked result.freshWire)
        splitWire member)).val =
      splitWire.val
  rw [DenseList.get_index]

def sourceWireOfRetained
    (result : WireSeverResult source wire keep scope)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    source.val.WireId :=
  ⟨splitWire.val, by
    have bound := splitWire.isLt
    have freshValue : result.freshWire.val = source.val.wireCount := by
      unfold freshWire Internal.checkedWire
      simp only [Fin.coe_cast, Fin.val_natAdd]
      omega
    have notLast : splitWire.val ≠ source.val.wireCount := by
      intro same
      apply survives
      apply Fin.ext
      exact same.trans freshValue.symm
    have count := result.wireCount
    omega⟩

@[simp] theorem wireImage_sourceWireOfRetained
    (result : WireSeverResult source wire keep scope)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    result.wireImage (result.sourceWireOfRetained splitWire survives) =
      splitWire := by
  apply Fin.ext
  rfl

@[simp] theorem sourceWireOfRetained_wireImage
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    result.sourceWireOfRetained (result.wireImage sourceWire)
        (retained_ne_fresh result sourceWire) =
      sourceWire := by
  apply Fin.ext
  rfl

private def inverseWire
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId) :
    result.inverseJoin.checked.val.WireId :=
  result.inverseJoin.wireImage (result.wireImage sourceWire)
    (retained_ne_fresh result sourceWire)

private def originalWire
    (result : WireSeverResult source wire keep scope)
    (target : result.inverseJoin.checked.val.WireId) :
    source.val.WireId :=
  result.sourceWireOfRetained (result.rejoinSourceWire target)
    (result.rejoinSourceWire_survives target)

private def regionEquiv
    (result : WireSeverResult source wire keep scope) :
    Data.Finite.FiniteEquiv source.val.RegionId
      result.inverseJoin.checked.val.RegionId where
  toFun := result.inverseRegion
  invFun := Fin.cast result.inverseJoin_regionCount
  left_inv := by
    intro region
    apply Fin.ext
    rfl
  right_inv := by
    intro region
    apply Fin.ext
    rfl

private def nodeEquiv
    (result : WireSeverResult source wire keep scope) :
    Data.Finite.FiniteEquiv source.val.NodeId
      result.inverseJoin.checked.val.NodeId where
  toFun := result.inverseNode
  invFun := Fin.cast result.inverseJoin_nodeCount
  left_inv := by
    intro node
    apply Fin.ext
    rfl
  right_inv := by
    intro node
    apply Fin.ext
    rfl

private def wireEquiv
    (result : WireSeverResult source wire keep scope) :
    Data.Finite.FiniteEquiv source.val.WireId
      result.inverseJoin.checked.val.WireId where
  toFun := result.inverseWire
  invFun := result.originalWire
  left_inv := by
    intro sourceWire
    unfold originalWire inverseWire
    calc
      result.sourceWireOfRetained
            (result.rejoinSourceWire
              (result.inverseJoin.wireImage
                (result.wireImage sourceWire) _)) _ =
          result.sourceWireOfRetained (result.wireImage sourceWire) _ := by
        congr 1
        exact result.rejoinSourceWire_wireImage
          (result.wireImage sourceWire) _
      _ = sourceWire :=
        result.sourceWireOfRetained_wireImage sourceWire
  right_inv := by
    intro target
    unfold inverseWire originalWire
    calc
      result.inverseJoin.wireImage
            (result.wireImage
              (result.sourceWireOfRetained
                (result.rejoinSourceWire target) _)) _ =
          result.inverseJoin.wireImage
            (result.rejoinSourceWire target) _ := by
        congr 1
      _ = target := result.inverseJoin_wireImage_sourceWire target

private def inverseEndpoint
    (result : WireSeverResult source wire keep scope)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.inverseJoin.checked.val.nodeCount :=
  ⟨result.inverseNode endpoint.node, endpoint.port⟩

private theorem inverseEndpoint_injective
    (result : WireSeverResult source wire keep scope) :
    Function.Injective result.inverseEndpoint := by
  intro left right same
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          have nodeSame : leftNode = rightNode := by
            apply Fin.ext
            exact congrArg (fun endpoint => endpoint.node.val) same
          have portSame : leftPort = rightPort :=
            congrArg (fun endpoint => endpoint.port) same
          subst rightNode
          subst rightPort
          rfl

@[simp] private theorem inverse_endpointImage
    (result : WireSeverResult source wire keep scope)
    (endpoint : CEndpoint source.val.nodeCount) :
    result.inverseJoin.endpointImage (result.endpointImage endpoint) =
      result.inverseEndpoint endpoint := by
  cases endpoint
  congr

private theorem mem_map_injective
    {map : α → β} (injective : Function.Injective map)
    (value : α) (values : List α) :
    map value ∈ values.map map ↔ value ∈ values := by
  constructor
  · intro member
    obtain ⟨candidate, candidateMember, same⟩ :=
      List.mem_map.mp member
    exact (injective same).symm ▸ candidateMember
  · exact fun member => List.mem_map.mpr ⟨value, member, rfl⟩

private theorem inverse_region_table
    (result : WireSeverResult source wire keep scope)
    (region : source.val.RegionId) :
    result.inverseJoin.checked.val.regions (result.inverseRegion region) =
      (source.val.regions region).rename result.regionEquiv := by
  rw [← inverse_regionImage, result.inverseJoin.region_generated,
    result.region_generated]
  cases source.val.regions region <;> rfl

private theorem inverse_node_table
    (result : WireSeverResult source wire keep scope)
    (node : source.val.NodeId) :
    result.inverseJoin.checked.val.nodes (result.inverseNode node) =
      (source.val.nodes node).rename result.regionEquiv := by
  rw [← inverse_nodeImage, result.inverseJoin.node_generated,
    result.node_generated]
  cases source.val.nodes node <;> rfl

private theorem inverseEndpoint_corresponds
    (result : WireSeverResult source wire keep scope)
    (endpoint : CEndpoint source.val.nodeCount)
    (required :
      endpoint.port ∈ source.val.requiredPorts endpoint.node) :
    PortCorresponds source.val result.inverseJoin.checked.val
      result.nodeEquiv endpoint (result.inverseEndpoint endpoint) := by
  unfold PortCorresponds
  constructor
  · rfl
  · simp only [inverseEndpoint]
    rw [result.inverse_node_table]
    cases data : source.val.nodes endpoint.node <;>
      simp [data, CNode.rename]
    rcases (by
      simpa [ConcreteDiagram.requiredPorts, data, eq_comm] using required) with
      ⟨index, _, port⟩
    exact ⟨index, port⟩

private theorem inverseEndpoint_mem
    (result : WireSeverResult source wire keep scope)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount) :
    result.inverseEndpoint endpoint ∈
        (result.inverseJoin.checked.val.wires
          (result.inverseWire sourceWire)).endpoints ↔
      endpoint ∈ (source.val.wires sourceWire).endpoints := by
  unfold inverseWire
  rw [result.inverseJoin.wireImage_endpoints]
  by_cases same : sourceWire = wire
  · subst sourceWire
    rw [if_pos rfl, result.wireImage_endpoints, if_pos rfl,
      result.freshWire_endpoints, List.map_append,
      List.map_map, List.map_map]
    change
      result.inverseEndpoint endpoint ∈
          ((source.val.wires wire).endpoints.filter fun candidate =>
              decide (candidate ∈ keep)).map result.inverseEndpoint ++
            ((source.val.wires wire).endpoints.filter fun candidate =>
              decide (candidate ∉ keep)).map result.inverseEndpoint ↔
        endpoint ∈ (source.val.wires wire).endpoints
    rw [List.mem_append,
      mem_map_injective result.inverseEndpoint_injective endpoint
        ((source.val.wires wire).endpoints.filter fun candidate =>
          decide (candidate ∈ keep)),
      mem_map_injective result.inverseEndpoint_injective endpoint
        ((source.val.wires wire).endpoints.filter fun candidate =>
          decide (candidate ∉ keep))]
    by_cases kept : endpoint ∈ keep <;> simp [kept]
  · have splitDifferent :
        result.wireImage sourceWire ≠ result.wireImage wire := by
      intro equal
      apply same
      apply Fin.ext
      simpa [WireSeverResult.wireImage, Internal.checkedWire] using
        congrArg Fin.val equal
    rw [if_neg splitDifferent, result.wireImage_endpoints,
      if_neg same, List.map_map]
    change
      result.inverseEndpoint endpoint ∈
          (source.val.wires sourceWire).endpoints.map
            result.inverseEndpoint ↔
        endpoint ∈ (source.val.wires sourceWire).endpoints
    exact
      mem_map_injective result.inverseEndpoint_injective endpoint
        (source.val.wires sourceWire).endpoints

/--
The canonical inverse join differs from the sever source only by endpoint
list order, which raw concrete isomorphism intentionally treats as
nonsemantic.
-/
def inverseIso
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    {scope : source.val.RegionId}
    (result : WireSeverResult source wire keep scope) :
    ConcreteIso source.val result.inverseJoin.checked.val where
  regions := result.regionEquiv
  nodes := result.nodeEquiv
  wires := result.wireEquiv
  root := by
    change
      result.inverseRegion source.val.root =
        result.inverseJoin.checked.val.root
    rw [← inverse_regionImage, ← result.root_generated,
      ← result.inverseJoin.root_generated]
  region_table := result.inverse_region_table
  node_table := result.inverse_node_table
  wire_signature := by
    intro sourceWire
    change
      (result.inverseJoin.checked.val.wires
        (result.inverseWire sourceWire)).sig =
        (source.val.wires sourceWire).sig
    unfold inverseWire
    rw [result.inverseJoin.wireImage_signature,
      result.wireImage_signature]
  wire_scope := by
    intro sourceWire
    change
      (result.inverseJoin.checked.val.wires
          (result.inverseWire sourceWire)).scope =
        result.inverseRegion (source.val.wires sourceWire).scope
    unfold inverseWire
    rw [result.inverseJoin.wireImage_scope,
      result.wireImage_scope, inverse_regionImage]
  endpointMap := fun _ endpoint => result.inverseEndpoint endpoint
  endpointInverse := fun _ candidate =>
    ⟨Fin.cast result.inverseJoin_nodeCount candidate.node, candidate.port⟩
  endpointMap_mem := by
    intro sourceWire endpoint incident
    exact (result.inverseEndpoint_mem sourceWire endpoint).mpr incident
  endpointInverse_mem := by
    intro sourceWire candidate incident
    let endpoint : CEndpoint source.val.nodeCount :=
      ⟨Fin.cast result.inverseJoin_nodeCount candidate.node, candidate.port⟩
    have endpointImage : result.inverseEndpoint endpoint = candidate := by
      cases candidate
      congr
    have mappedIncident :
        result.inverseEndpoint endpoint ∈
          (result.inverseJoin.checked.val.wires
            (result.inverseWire sourceWire)).endpoints :=
      endpointImage ▸ incident
    have sourceIncident :
        endpoint ∈ (source.val.wires sourceWire).endpoints :=
      (result.inverseEndpoint_mem sourceWire endpoint).mp mappedIncident
    exact sourceIncident
  endpointMap_left_inv := by
    rintro sourceWire ⟨node, port⟩ incident
    change (⟨Fin.cast result.inverseJoin_nodeCount
      (result.inverseNode node), port⟩ :
        CEndpoint source.val.nodeCount) = ⟨node, port⟩
    congr 1
  endpointMap_right_inv := by
    rintro sourceWire ⟨node, port⟩ incident
    change result.inverseEndpoint
      ⟨Fin.cast result.inverseJoin_nodeCount node, port⟩ =
        (⟨node, port⟩ :
          CEndpoint result.inverseJoin.checked.val.nodeCount)
    congr 1
  endpointMap_corresponds := by
    intro sourceWire endpoint incident
    exact result.inverseEndpoint_corresponds endpoint
      (ConcreteDiagram.incident_port_required definitions source.val
        source.property sourceWire endpoint incident)

end WireSeverResult

/--
Merge the inner individual wire into the retained outer wire and delete the
inner identifier. Scope comparability is intentionally rule-owned.
-/
def joinWires
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) :
    Except Error (WireJoinResult source outer inner) := by
  if same : outer = inner then
    exact .error .sameWire
  else if signaturesEqual :
      (source.val.wires outer).sig = (source.val.wires inner).sig then
    let candidate := wireJoinCandidate source outer inner
    match accepted :
        ConcreteDiagram.checkWellFormed definitions candidate with
    | .error error =>
        exact .error (.wellFormed error)
    | .ok checked =>
        exact .ok
          (WireJoinResult.mk checked same signaturesEqual
            (ConcreteDiagram.checkWellFormed_preserves_input accepted))
  else
    exact .error .signatureMismatch

end ConcreteWireQuantifier

end VisualProof
