import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval

namespace VisualProof

namespace ConcreteWireQuantifier

private def iotaSeverCandidate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount)) :
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
          endpoints := data.endpoints.filter fun endpoint =>
            decide (endpoint ∉ keep) })

private def iotaJoinWires
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

private def iotaJoinCandidate
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) :
    ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount
  wireCount := (iotaJoinWires source inner).length
  root := source.val.root
  regions := source.val.regions
  nodes := source.val.nodes
  wires := fun target =>
    let sourceWire := (iotaJoinWires source inner).get target
    let data := source.val.wires sourceWire
    if sourceWire = outer then
      { data with
        endpoints :=
          data.endpoints ++ (source.val.wires inner).endpoints }
    else
      data

/-- Checked output of one individual-wire endpoint partition. -/
structure IotaSeverResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount)) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private sourceSignature : (source.val.wires wire).sig = .iota
  private generated :
    checked.val = iotaSeverCandidate source wire keep
  private rejoined : CheckedDiagram definitions
  private rejoinedGenerated :
    rejoined.val =
      iotaJoinCandidate checked
        (Internal.checkedWire generated (Fin.castAdd 1 wire))
        (Internal.checkedWire generated
          (Fin.natAdd source.val.wireCount (0 : Fin 1)))

namespace IotaSeverResult

def regionImage
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated region

def nodeImage
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated node

def wireImage
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated (Fin.castAdd 1 sourceWire)

def freshWire
    (result : IotaSeverResult source wire keep) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.natAdd source.val.wireCount (0 : Fin 1))

def endpointImage
    (result : IotaSeverResult source wire keep)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.checked.val.nodeCount :=
  Internal.checkedEndpoint result.generated endpoint

def renameRegion
    (result : IotaSeverResult source wire keep) :
    CRegion source.val.regionCount →
      CRegion result.checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (result.regionImage parent)

def renameNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    (result : IotaSeverResult source wire keep) :
    CNode source.val.regionCount definitions.length →
      CNode result.checked.val.regionCount definitions.length
  | .atom region args => .atom (result.regionImage region) args
  | .ref region definition args =>
      .ref (result.regionImage region) definition args
  | .identity region sig arity =>
      .identity (result.regionImage region) sig arity

theorem checked_generated
    (result : IotaSeverResult source wire keep) :
    result.checked.val = iotaSeverCandidate source wire keep :=
  result.generated

@[simp] theorem regionCount
    (result : IotaSeverResult source wire keep) :
    result.checked.val.regionCount = source.val.regionCount :=
  by
    simpa [iotaSeverCandidate] using
      congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : IotaSeverResult source wire keep) :
    result.checked.val.nodeCount = source.val.nodeCount :=
  by
    simpa [iotaSeverCandidate] using
      congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : IotaSeverResult source wire keep) :
    result.checked.val.wireCount = source.val.wireCount + 1 :=
  by
    simpa [iotaSeverCandidate] using
      congrArg ConcreteDiagram.wireCount result.generated

@[simp] theorem root_generated
    (result : IotaSeverResult source wire keep) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  rw [Internal.checkedRoot_transport]
  rfl

@[simp] theorem region_generated
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionImage region) =
      result.renameRegion (source.val.regions region) := by
  unfold regionImage renameRegion
  rw [Internal.checkedRegion_data_transport]
  simp only [iotaSeverCandidate]
  cases source.val.regions region <;> rfl

theorem climb_regionImage
    (result : IotaSeverResult source wire keep)
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
          simp only [IotaSeverResult.renameRegion]
          exact induction parent

@[simp] theorem node_generated
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.checked.val.nodes (result.nodeImage node) =
      result.renameNode (source.val.nodes node) := by
  unfold nodeImage renameNode
  rw [Internal.checkedNode_data_transport]
  simp only [iotaSeverCandidate]
  cases source.val.nodes node <;> rfl

@[simp] theorem wireImage_signature
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  unfold wireImage
  rw [Internal.checkedWire_signature_transport]
  simp [iotaSeverCandidate]
  split <;> rfl

@[simp] theorem freshWire_signature
    (result : IotaSeverResult source wire keep) :
    (result.checked.val.wires result.freshWire).sig = .iota := by
  unfold freshWire
  rw [Internal.checkedWire_signature_transport]
  simpa [iotaSeverCandidate] using result.sourceSignature

@[simp] theorem wireImage_scope
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold wireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  simp [iotaSeverCandidate]
  split <;> rfl

@[simp] theorem freshWire_scope
    (result : IotaSeverResult source wire keep) :
    (result.checked.val.wires result.freshWire).scope =
      result.regionImage (source.val.wires wire).scope := by
  unfold freshWire regionImage
  rw [Internal.checkedWire_scope_transport]
  simp only [iotaSeverCandidate, Fin.addCases_right]

theorem wireImage_endpoints
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).endpoints =
      (if sourceWire = wire then
        (source.val.wires sourceWire).endpoints.filter fun endpoint =>
          decide (endpoint ∈ keep)
      else
        (source.val.wires sourceWire).endpoints).map result.endpointImage := by
  unfold wireImage endpointImage
  rw [Internal.checkedWire_endpoints_transport]
  simp only [iotaSeverCandidate, Fin.addCases_left]
  split <;> rfl

theorem freshWire_endpoints
    (result : IotaSeverResult source wire keep) :
    (result.checked.val.wires result.freshWire).endpoints =
      ((source.val.wires wire).endpoints.filter fun endpoint =>
        decide (endpoint ∉ keep)).map result.endpointImage := by
  unfold freshWire endpointImage
  rw [Internal.checkedWire_endpoints_transport]
  simp only [iotaSeverCandidate, Fin.addCases_right]

end IotaSeverResult

/--
Split one individual wire into two co-scoped wires according to an exact
endpoint partition. Polarity and orientation are intentionally rule-owned.
-/
def severIota
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount)) :
    Except Error (IotaSeverResult source wire keep) := by
  if signature : (source.val.wires wire).sig = .iota then
    if partition :
        ∀ endpoint, endpoint ∈ keep →
          endpoint ∈ (source.val.wires wire).endpoints then
      let candidate := iotaSeverCandidate source wire keep
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
            iotaJoinCandidate checked retained fresh
          match rejoinAccepted :
              ConcreteDiagram.checkWellFormed definitions rejoinCandidate with
          | .error error =>
              exact .error (.wellFormed error)
          | .ok rejoined =>
              exact .ok
                (IotaSeverResult.mk checked signature generated rejoined
                  (ConcreteDiagram.checkWellFormed_preserves_input
                    rejoinAccepted))
    else
      exact .error .invalidEndpointPartition
  else
    exact .error (.expectedIota wire.val)

/-- Checked output of one comparable-scope individual-wire merge. -/
structure IotaJoinResult
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private different : outer ≠ inner
  private outerSignature : (source.val.wires outer).sig = .iota
  private innerSignature : (source.val.wires inner).sig = .iota
  private generated :
    checked.val = iotaJoinCandidate source outer inner

namespace IotaJoinResult

def regionImage
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated region

def nodeImage
    (result : IotaJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated node

def wireImage
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (DenseList.index (iotaJoinWires source inner) sourceWire (by
      simp [iotaJoinWires, ConcreteDiagram.wiresList,
        Data.Finite.mem_allFin, survives]))

def outerWire
    (result : IotaJoinResult source outer inner) :
    result.checked.val.WireId :=
  result.wireImage outer result.different

def endpointImage
    (result : IotaJoinResult source outer inner)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.checked.val.nodeCount :=
  Internal.checkedEndpoint result.generated endpoint

def renameRegion
    (result : IotaJoinResult source outer inner) :
    CRegion source.val.regionCount →
      CRegion result.checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (result.regionImage parent)

def renameNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner) :
    CNode source.val.regionCount definitions.length →
      CNode result.checked.val.regionCount definitions.length
  | .atom region args => .atom (result.regionImage region) args
  | .ref region definition args =>
      .ref (result.regionImage region) definition args
  | .identity region sig arity =>
      .identity (result.regionImage region) sig arity

theorem checked_generated
    (result : IotaJoinResult source outer inner) :
    result.checked.val = iotaJoinCandidate source outer inner :=
  result.generated

theorem outer_ne_inner
    (result : IotaJoinResult source outer inner) :
    outer ≠ inner :=
  result.different

@[simp] theorem source_outer_signature
    (result : IotaJoinResult source outer inner) :
    (source.val.wires outer).sig = .iota :=
  result.outerSignature

@[simp] theorem source_inner_signature
    (result : IotaJoinResult source outer inner) :
    (source.val.wires inner).sig = .iota :=
  result.innerSignature

@[simp] theorem regionCount
    (result : IotaJoinResult source outer inner) :
    result.checked.val.regionCount = source.val.regionCount := by
  simpa [iotaJoinCandidate] using
    congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : IotaJoinResult source outer inner) :
    result.checked.val.nodeCount = source.val.nodeCount := by
  simpa [iotaJoinCandidate] using
    congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : IotaJoinResult source outer inner) :
    result.checked.val.wireCount = (iotaJoinWires source inner).length := by
  simpa [iotaJoinCandidate] using
    congrArg ConcreteDiagram.wireCount result.generated

@[simp] theorem root_generated
    (result : IotaJoinResult source outer inner) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  rw [Internal.checkedRoot_transport]
  rfl

@[simp] theorem region_generated
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionImage region) =
      result.renameRegion (source.val.regions region) := by
  unfold regionImage renameRegion
  rw [Internal.checkedRegion_data_transport]
  simp only [iotaJoinCandidate]
  cases source.val.regions region <;> rfl

@[simp] theorem node_generated
    (result : IotaJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.checked.val.nodes (result.nodeImage node) =
      result.renameNode (source.val.nodes node) := by
  unfold nodeImage renameNode
  rw [Internal.checkedNode_data_transport]
  simp only [iotaJoinCandidate]
  cases source.val.nodes node <;> rfl

@[simp] theorem wireImage_signature
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).sig =
      (source.val.wires sourceWire).sig := by
  unfold wireImage
  rw [Internal.checkedWire_signature_transport]
  simp only [iotaJoinCandidate]
  rw [DenseList.get_index]
  split <;> rfl

@[simp] theorem wireImage_scope
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold wireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  simp only [iotaJoinCandidate]
  rw [DenseList.get_index]
  split <;> rfl

theorem wireImage_endpoints
    (result : IotaJoinResult source outer inner)
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
  simp only [iotaJoinCandidate]
  rw [DenseList.get_index]
  split
  · rename_i same
    subst sourceWire
    rfl
  · rfl

end IotaJoinResult

namespace IotaSeverResult

/--
The checker-owned inverse join of an accepted iota sever. Its checked target
is the canonical stable-partition rejoin retained by the sever receipt.
-/
def inverseJoin
    (result : IotaSeverResult source wire keep) :
    IotaJoinResult result.checked (result.wireImage wire)
      result.freshWire :=
  IotaJoinResult.mk result.rejoined (by
    intro same
    have values := congrArg Fin.val same
    unfold wireImage freshWire Internal.checkedWire at values
    simp only [Fin.coe_cast, Fin.val_castAdd, Fin.val_natAdd] at values
    omega)
    (by
      rw [result.wireImage_signature]
      exact result.sourceSignature)
    result.freshWire_signature
    (by
      simpa [wireImage, freshWire] using result.rejoinedGenerated)

@[simp] theorem inverseJoin_checked
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked = result.rejoined :=
  rfl

@[simp] theorem inverseJoin_regionCount
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked.val.regionCount = source.val.regionCount := by
  rw [result.inverseJoin.regionCount, result.regionCount]

@[simp] theorem inverseJoin_nodeCount
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked.val.nodeCount = source.val.nodeCount := by
  rw [result.inverseJoin.nodeCount, result.nodeCount]

@[simp] theorem inverseJoin_wireCount
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked.val.wireCount = source.val.wireCount := by
  rw [result.inverseJoin.wireCount]
  unfold iotaJoinWires
  unfold ConcreteDiagram.wiresList
  rw [filter_ne_length_of_nodup_mem
    (Data.Finite.allFin_nodup result.checked.val.wireCount)
    (Data.Finite.mem_allFin result.freshWire)]
  simp only [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange,
    List.length_finRange]
  rw [result.wireCount]
  omega

private def inverseRegion
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.inverseJoin.checked.val.RegionId :=
  Fin.cast result.inverseJoin_regionCount.symm region

private def inverseNode
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.inverseJoin.checked.val.NodeId :=
  Fin.cast result.inverseJoin_nodeCount.symm node

@[simp] private theorem inverse_regionImage
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.inverseJoin.regionImage (result.regionImage region) =
      result.inverseRegion region := by
  apply Fin.ext
  rfl

@[simp] private theorem inverse_nodeImage
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.inverseJoin.nodeImage (result.nodeImage node) =
      result.inverseNode node := by
  apply Fin.ext
  rfl

private theorem retained_ne_fresh
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.wireImage sourceWire ≠ result.freshWire := by
  intro same
  have values := congrArg Fin.val same
  unfold wireImage freshWire Internal.checkedWire at values
  simp only [Fin.coe_cast, Fin.val_castAdd, Fin.val_natAdd] at values
  omega

private def rejoinSourceWire
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    result.checked.val.WireId :=
  (iotaJoinWires result.checked result.freshWire).get
    (Fin.cast result.inverseJoin.wireCount target)

private theorem rejoinSourceWire_survives
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    result.rejoinSourceWire target ≠ result.freshWire := by
  have member :
      result.rejoinSourceWire target ∈
        iotaJoinWires result.checked result.freshWire :=
    List.get_mem _ _
  exact of_decide_eq_true (List.mem_filter.mp member).2

@[simp] private theorem inverseJoin_wireImage_sourceWire
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    result.inverseJoin.wireImage (result.rejoinSourceWire target)
        (result.rejoinSourceWire_survives target) =
      target := by
  unfold IotaJoinResult.wireImage rejoinSourceWire
  apply Fin.ext
  change
    (DenseList.index
      (iotaJoinWires result.checked result.freshWire)
      ((iotaJoinWires result.checked result.freshWire).get
        (Fin.cast result.inverseJoin.wireCount target)) _).val =
      target.val
  rw [DenseList.index_get
    (iotaJoinWires result.checked result.freshWire)
    ((Data.Finite.allFin_nodup result.checked.val.wireCount).filter _)
    (Fin.cast result.inverseJoin.wireCount target)]
  rfl

@[simp] private theorem rejoinSourceWire_wireImage
    (result : IotaSeverResult source wire keep)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    result.rejoinSourceWire
        (result.inverseJoin.wireImage splitWire survives) =
      splitWire := by
  have member :
      splitWire ∈ iotaJoinWires result.checked result.freshWire := by
    simp [iotaJoinWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  unfold rejoinSourceWire IotaJoinResult.wireImage
  apply Fin.ext
  change
    ((iotaJoinWires result.checked result.freshWire).get
      (DenseList.index
        (iotaJoinWires result.checked result.freshWire)
        splitWire member)).val =
      splitWire.val
  rw [DenseList.get_index]

private def sourceWireOfRetained
    (result : IotaSeverResult source wire keep)
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

@[simp] private theorem wireImage_sourceWireOfRetained
    (result : IotaSeverResult source wire keep)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    result.wireImage (result.sourceWireOfRetained splitWire survives) =
      splitWire := by
  apply Fin.ext
  rfl

@[simp] private theorem sourceWireOfRetained_wireImage
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.sourceWireOfRetained (result.wireImage sourceWire)
        (retained_ne_fresh result sourceWire) =
      sourceWire := by
  apply Fin.ext
  rfl

private def inverseWire
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.inverseJoin.checked.val.WireId :=
  result.inverseJoin.wireImage (result.wireImage sourceWire)
    (retained_ne_fresh result sourceWire)

private def originalWire
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    source.val.WireId :=
  result.sourceWireOfRetained (result.rejoinSourceWire target)
    (result.rejoinSourceWire_survives target)

private def regionEquiv
    (result : IotaSeverResult source wire keep) :
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
    (result : IotaSeverResult source wire keep) :
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
    (result : IotaSeverResult source wire keep) :
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
    (result : IotaSeverResult source wire keep)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.inverseJoin.checked.val.nodeCount :=
  ⟨result.inverseNode endpoint.node, endpoint.port⟩

private theorem inverseEndpoint_injective
    (result : IotaSeverResult source wire keep) :
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
    (result : IotaSeverResult source wire keep)
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
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.inverseJoin.checked.val.regions (result.inverseRegion region) =
      (source.val.regions region).rename result.regionEquiv := by
  rw [← inverse_regionImage, result.inverseJoin.region_generated,
    result.region_generated]
  cases source.val.regions region <;> rfl

private theorem inverse_node_table
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.inverseJoin.checked.val.nodes (result.inverseNode node) =
      (source.val.nodes node).rename result.regionEquiv := by
  rw [← inverse_nodeImage, result.inverseJoin.node_generated,
    result.node_generated]
  cases source.val.nodes node <;> rfl

private theorem inverseEndpoint_corresponds
    (result : IotaSeverResult source wire keep)
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
    (result : IotaSeverResult source wire keep)
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
      simpa [IotaSeverResult.wireImage, Internal.checkedWire] using
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
    (result : IotaSeverResult source wire keep) :
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
  endpoint_forward := by
    intro sourceWire endpoint incident
    refine
      ⟨result.inverseEndpoint endpoint,
        (result.inverseEndpoint_mem sourceWire endpoint).mpr incident, ?_⟩
    exact
      result.inverseEndpoint_corresponds endpoint
        (ConcreteDiagram.incident_port_required definitions source.val
          source.property sourceWire endpoint incident)
  endpoint_backward := by
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
    refine ⟨endpoint, sourceIncident, ?_⟩
    have corresponds :=
      result.inverseEndpoint_corresponds endpoint
        (ConcreteDiagram.incident_port_required definitions source.val
          source.property sourceWire endpoint sourceIncident)
    exact endpointImage ▸ corresponds

end IotaSeverResult

/--
Merge the inner individual wire into the retained outer wire and delete the
inner identifier. Scope comparability is intentionally rule-owned.
-/
def joinIota
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) :
    Except Error (IotaJoinResult source outer inner) := by
  if same : outer = inner then
    exact .error .sameWire
  else if outerSignature : (source.val.wires outer).sig = .iota then
    if innerSignature : (source.val.wires inner).sig = .iota then
      let candidate := iotaJoinCandidate source outer inner
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          exact .ok
            (IotaJoinResult.mk checked same outerSignature innerSignature
              (ConcreteDiagram.checkWellFormed_preserves_input accepted))
    else
      exact .error (.expectedIota inner.val)
  else
    exact .error (.expectedIota outer.val)

end ConcreteWireQuantifier

end VisualProof
