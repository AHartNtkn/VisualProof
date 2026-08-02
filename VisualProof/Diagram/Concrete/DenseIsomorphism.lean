import VisualProof.Diagram.Concrete.Isomorphism

namespace VisualProof

open Data.Finite

/--
A construction-owned concrete isomorphism whose three carrier maps preserve
the canonical dense index.  The underlying `ConcreteIso` remains the owner of
all graph tables and endpoint fibers; density is additional provenance used by
deterministic constructions that inspect finite identifiers in order.
-/
structure DenseConcreteIso {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length) where
  iso : ConcreteIso left right
  region_val : ∀ region, (iso.regions region).val = region.val
  node_val : ∀ node, (iso.nodes node).val = node.val
  wire_val : ∀ wire, (iso.wires wire).val = wire.val

namespace DenseConcreteIso

/-- The canonical value-preserving equivalence induced by equal finite counts. -/
def finEquivOfEq {leftCount rightCount : Nat}
    (count_eq : leftCount = rightCount) :
    FiniteEquiv (Fin leftCount) (Fin rightCount) := by
  subst rightCount
  exact FiniteEquiv.refl _

@[simp] theorem finEquivOfEq_val
    {leftCount rightCount : Nat}
    (count_eq : leftCount = rightCount)
    (value : Fin leftCount) :
    (finEquivOfEq count_eq value).val = value.val := by
  subst rightCount
  rfl

instance {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length} :
    Coe (DenseConcreteIso left right) (ConcreteIso left right) :=
  ⟨DenseConcreteIso.iso⟩

/-- Forget only the dense-index provenance. -/
def toConcreteIso
    (dense : DenseConcreteIso left right) : ConcreteIso left right :=
  dense.iso

/-- Identity isomorphism on a checked concrete diagram. -/
def refl
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    DenseConcreteIso diagram diagram where
  iso :=
    { regions := FiniteEquiv.refl _
      nodes := FiniteEquiv.refl _
      wires := FiniteEquiv.refl _
      root := rfl
      region_table := by
        intro region
        cases data : diagram.regions region <;>
          simp [FiniteEquiv.refl_apply, CRegion.rename, data]
      node_table := by
        intro node
        cases data : diagram.nodes node <;>
          simp [FiniteEquiv.refl_apply, CNode.rename, data]
      wire_signature := by intro; rfl
      wire_scope := by intro; rfl
      endpointMap := fun _ endpoint => endpoint
      endpointInverse := fun _ endpoint => endpoint
      endpointMap_mem := by intros; assumption
      endpointInverse_mem := by intros; assumption
      endpointMap_left_inv := by intros; rfl
      endpointMap_right_inv := by intros; rfl
      endpointMap_corresponds := by
        intro wire endpoint incident
        unfold PortCorresponds
        constructor
        · rfl
        · have required := ConcreteDiagram.incident_port_required definitions
            diagram wellFormed wire endpoint incident
          cases nodeData : diagram.nodes endpoint.node with
          | atom => simp
          | ref => simp
          | identity region signature arity =>
              simp [ConcreteDiagram.requiredPorts, nodeData] at required
              obtain ⟨index, _, exact⟩ := required
              exact ⟨rfl, rfl, index, index, exact.symm, exact.symm⟩ }
  region_val := by intro; rfl
  node_val := by intro; rfl
  wire_val := by intro; rfl

/-- Reverse a dense isomorphism without rediscovering any correspondence. -/
def symm
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right) :
    DenseConcreteIso right left where
  iso := dense.iso.symm
  region_val := by
    intro region
    let source := dense.iso.regions.symm region
    have forwardValue := dense.region_val source
    have roundtrip := congrArg Fin.val (dense.iso.regions.right_inv region)
    exact forwardValue.symm.trans roundtrip
  node_val := by
    intro node
    let source := dense.iso.nodes.symm node
    have forwardValue := dense.node_val source
    have roundtrip := congrArg Fin.val (dense.iso.nodes.right_inv node)
    exact forwardValue.symm.trans roundtrip
  wire_val := by
    intro wire
    let source := dense.iso.wires.symm wire
    have forwardValue := dense.wire_val source
    have roundtrip := congrArg Fin.val (dense.iso.wires.right_inv wire)
    exact forwardValue.symm.trans roundtrip

/-- Compose dense construction receipts algebraically. -/
def trans
    {definitions : List (List Sig)}
    {first second third : ConcreteDiagram definitions.length}
    (left : DenseConcreteIso first second)
    (right : DenseConcreteIso second third) :
    DenseConcreteIso first third where
  iso := left.iso.trans right.iso
  region_val := by
    intro region
    exact (right.region_val (left.iso.regions region)).trans
      (left.region_val region)
  node_val := by
    intro node
    exact (right.node_val (left.iso.nodes node)).trans
      (left.node_val node)
  wire_val := by
    intro wire
    exact (right.wire_val (left.iso.wires wire)).trans
      (left.wire_val wire)

@[simp] theorem symm_region_val
    (dense : DenseConcreteIso left right)
    (region : right.RegionId) :
    ((dense.symm).iso.regions region).val = region.val :=
  (dense.symm).region_val region

@[simp] theorem symm_node_val
    (dense : DenseConcreteIso left right)
    (node : right.NodeId) :
    ((dense.symm).iso.nodes node).val = node.val :=
  (dense.symm).node_val node

@[simp] theorem symm_wire_val
    (dense : DenseConcreteIso left right)
    (wire : right.WireId) :
    ((dense.symm).iso.wires wire).val = wire.val :=
  (dense.symm).wire_val wire

/-- Dense isomorphisms preserve the canonical ordered region carrier. -/
theorem map_regionsList
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right) :
    left.regionsList.map dense.iso.regions = right.regionsList := by
  apply List.ext_get
  · simpa only [List.length_map, ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange, List.length_finRange] using
      dense.iso.regionCount_eq
  · intro index leftBound rightBound
    apply Fin.ext
    simpa [ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange] using
      dense.region_val
        ((left.regionsList).get ⟨index, by simpa using leftBound⟩)

/-- Dense isomorphisms preserve the canonical ordered node carrier. -/
theorem map_nodesList
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right) :
    left.nodesList.map dense.iso.nodes = right.nodesList := by
  apply List.ext_get
  · simpa only [List.length_map, ConcreteDiagram.nodesList,
      Data.Finite.allFin_eq_finRange, List.length_finRange] using
      dense.iso.nodeCount_eq
  · intro index leftBound rightBound
    apply Fin.ext
    simpa [ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange] using
      dense.node_val
        ((left.nodesList).get ⟨index, by simpa using leftBound⟩)

/-- Dense isomorphisms preserve the canonical ordered wire carrier. -/
theorem map_wiresList
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right) :
    left.wiresList.map dense.iso.wires = right.wiresList := by
  apply List.ext_get
  · simpa only [List.length_map, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange, List.length_finRange] using
      dense.iso.wireCount_eq
  · intro index leftBound rightBound
    apply Fin.ext
    simpa [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange] using
      dense.wire_val
        ((left.wiresList).get ⟨index, by simpa using leftBound⟩)

/-- Mapping an ordered boundary preserves its length exactly. -/
@[simp] theorem map_boundary_length
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (boundary : List left.WireId) :
    (boundary.map dense.iso.wires).length = boundary.length := by
  simp

/-- Every ordered boundary position keeps its dense wire index. -/
theorem map_boundary_get_val
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (dense : DenseConcreteIso left right)
    (boundary : List left.WireId)
    (position : Fin boundary.length) :
    ((boundary.map dense.iso.wires).get
      (Fin.cast (by simp) position)).val =
      (boundary.get position).val := by
  simpa using dense.wire_val (boundary.get position)

end DenseConcreteIso

end VisualProof
