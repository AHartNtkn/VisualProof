import VisualProof.Diagram.Concrete.WirePrimitive.Content

namespace VisualProof

open ConcreteWireQuantifier
open WirePrimitive

namespace ConcreteWirePrimitive

namespace CutWrapResult

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {wire : source.val.WireId}

/-- Neutral origin of a checked cut-wrap region: either a retained source
region or the generated cut for an ordered acted site. -/
abbrev RegionOrigin
    (result : CutWrapResult source wire) :=
  Sum source.val.RegionId (Fin result.sites.sites.length)

private def allocationRegionOriginEquiv
    (result : CutWrapResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin (source.val.regionCount + result.sites.sites.length))
      result.RegionOrigin where
  toFun := Fin.addCases Sum.inl Sum.inr
  invFun := Sum.elim
    (Fin.castAdd result.sites.sites.length)
    (Fin.natAdd source.val.regionCount)
  left_inv := by
    intro allocation
    refine Fin.addCases (fun region => ?_) (fun site => ?_) allocation
    · simp only [Fin.addCases_left, Sum.elim_inl]
    · simp only [Fin.addCases_right, Sum.elim_inr]
  right_inv := by
    intro origin
    rcases origin with region | site
    · rw [Sum.elim_inl, Fin.addCases_left]
    · rw [Sum.elim_inr, Fin.addCases_right]

/-- Complete neutral region-origin classifier for cut wrapping. -/
def regionOriginEquiv
    (result : CutWrapResult source wire) :
    Data.Finite.FiniteEquiv
      result.checked.val.RegionId result.RegionOrigin :=
  result.extendedRegionOriginEquiv.trans
    (allocationRegionOriginEquiv result)

@[simp] theorem regionOriginEquiv_targetRegion
    (result : CutWrapResult source wire)
    (region : source.val.RegionId) :
    result.regionOriginEquiv (result.targetRegion region) = Sum.inl region := by
  rw [regionOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.extendedRegionOriginEquiv_targetRegion]
  simp only [allocationRegionOriginEquiv, Fin.addCases_left]

@[simp] theorem regionOriginEquiv_targetCutRegion
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.regionOriginEquiv (result.targetCutRegion site) = Sum.inr site := by
  rw [regionOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.extendedRegionOriginEquiv_targetCutRegion]
  simp only [allocationRegionOriginEquiv, Fin.addCases_right]

end CutWrapResult

namespace ParallelSplitResult

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {wire : source.val.WireId}

/-- Neutral origin of a checked split node: either a retained source node or
an ordered site on the first or second generated branch. -/
abbrev NodeOrigin
    (result : ParallelSplitResult source wire) :=
  Sum { node : source.val.NodeId // node ∉ result.sourceRemovedNodes }
    (Sum (Fin result.sites.sites.length)
      (Fin result.sites.sites.length))

/-- Neutral origin of a checked split wire: either a retained source wire or
one of the two generated branches. -/
abbrev WireOrigin
    (result : ParallelSplitResult source wire) :=
  Sum { sourceWire : source.val.WireId //
      sourceWire ∉ result.sourceRemovedWires }
    (Fin 2)

private theorem retainedNode_not_removed
    (result : ParallelSplitResult source wire)
    (candidate : Fin result.retainedNodeCount) :
    Internal.sourceRetainedNode source result.sourceRemovedNodes candidate ∉
      result.sourceRemovedNodes := by
  have member := List.get_mem
    (Internal.retainedNodes source result.sourceRemovedNodes) candidate
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem retainedWire_not_removed
    (result : ParallelSplitResult source wire)
    (candidate : Fin result.retainedWireCount) :
    Internal.sourceRetainedWire source result.sourceRemovedWires candidate ∉
      result.sourceRemovedWires := by
  have member := List.get_mem
    (Internal.retainedWires source result.sourceRemovedWires) candidate
  exact of_decide_eq_true (List.mem_filter.mp member).2

private def allocationNodeOriginEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin result.nodeAllocationCount) result.NodeOrigin where
  toFun := Fin.addCases
    (fun retained => Sum.inl
      ⟨Internal.sourceRetainedNode source result.sourceRemovedNodes retained,
        retainedNode_not_removed result retained⟩)
    (Fin.addCases (fun site => Sum.inr (Sum.inl site))
      (fun site => Sum.inr (Sum.inr site)))
  invFun := fun origin => match origin with
    | .inl retained => Fin.castAdd
        (result.sites.sites.length + result.sites.sites.length)
        (Internal.retainedNodeIndex source result.sourceRemovedNodes
          retained.1 (by
            unfold Internal.retainedNodes
            exact List.mem_filter.mpr
              ⟨Data.Finite.mem_allFin retained.1,
                decide_eq_true retained.2⟩))
    | .inr (.inl site) => Fin.natAdd result.retainedNodeCount
        (Fin.castAdd result.sites.sites.length site)
    | .inr (.inr site) => Fin.natAdd result.retainedNodeCount
        (Fin.natAdd result.sites.sites.length site)
  left_inv := by
    intro allocation
    refine Fin.addCases (m := result.retainedNodeCount)
      (fun retained => ?_) (fun generated => ?_) allocation
    · apply Fin.ext
      simp [Internal.retainedNodeIndex_sourceRetainedNode]
    · refine Fin.addCases (m := result.sites.sites.length)
        (fun first => ?_) (fun second => ?_) generated
      · apply Fin.ext
        simp only [Fin.addCases_right, Fin.addCases_left]
      · apply Fin.ext
        simp only [Fin.addCases_right]
  right_inv := by
    intro origin
    rcases origin with retained | generated
    · simp only [Fin.addCases_left]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact Internal.sourceRetainedNode_retainedNodeIndex _ _ _ _
    · rcases generated with first | second
      · simp only [Fin.addCases_right, Fin.addCases_left]
      · simp only [Fin.addCases_right]

/-- Complete neutral node-origin classifier for parallel splitting. -/
def nodeOriginEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      result.checked.val.NodeId result.NodeOrigin :=
  result.constructionNodeEquiv.trans (allocationNodeOriginEquiv result)

@[simp] theorem nodeOriginEquiv_retainedNodeImage
    (result : ParallelSplitResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.nodeOriginEquiv (result.retainedNodeImage node retained) =
      Sum.inl ⟨node, retained⟩ := by
  rw [nodeOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.constructionNodeEquiv_retainedNodeImage]
  simp only [allocationNodeOriginEquiv, nodeAllocationCount,
    retainedNodeCount, Fin.addCases_left]
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Internal.sourceRetainedNode_retainedNodeIndex _ _ _ _

@[simp] theorem nodeOriginEquiv_firstNode
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) :
    result.nodeOriginEquiv (result.firstNode site) =
      Sum.inr (Sum.inl site) := by
  rw [nodeOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.constructionNodeEquiv_firstNode]
  simp only [allocationNodeOriginEquiv, nodeAllocationCount,
    retainedNodeCount, Fin.addCases_right, Fin.addCases_left]

@[simp] theorem nodeOriginEquiv_secondNode
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) :
    result.nodeOriginEquiv (result.secondNode site) =
      Sum.inr (Sum.inr site) := by
  rw [nodeOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.constructionNodeEquiv_secondNode]
  simp only [allocationNodeOriginEquiv, nodeAllocationCount,
    retainedNodeCount, Fin.addCases_right]

private def allocationWireOriginEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin result.wireAllocationCount) result.WireOrigin where
  toFun := Fin.addCases
    (fun retained => Sum.inl
      ⟨Internal.sourceRetainedWire source result.sourceRemovedWires retained,
        retainedWire_not_removed result retained⟩)
    Sum.inr
  invFun := fun origin => match origin with
    | .inl retained => Fin.castAdd 2
        (Internal.retainedWireIndex source result.sourceRemovedWires
          retained.1 (by
            unfold Internal.retainedWires
            exact List.mem_filter.mpr
              ⟨Data.Finite.mem_allFin retained.1,
                decide_eq_true retained.2⟩))
    | .inr branch => Fin.natAdd result.retainedWireCount branch
  left_inv := by
    intro allocation
    refine Fin.addCases (m := result.retainedWireCount)
      (fun retained => ?_) (fun branch => ?_) allocation
    · apply Fin.ext
      simp [Internal.retainedWireIndex_sourceRetainedWire]
    · apply Fin.ext
      simp
  right_inv := by
    intro origin
    rcases origin with retained | branch
    · simp only [Fin.addCases_left]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact Internal.sourceRetainedWire_retainedWireIndex _ _ _ _
    · simp only [Fin.addCases_right]

/-- Complete neutral wire-origin classifier for parallel splitting. -/
def wireOriginEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      result.checked.val.WireId result.WireOrigin :=
  result.constructionWireEquiv.trans (allocationWireOriginEquiv result)

@[simp] theorem wireOriginEquiv_retainedWireImage
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.wireOriginEquiv
        (result.retainedWireImage sourceWire retained) =
      Sum.inl ⟨sourceWire, retained⟩ := by
  rw [wireOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.constructionWireEquiv_retainedWireImage]
  simp only [allocationWireOriginEquiv, wireAllocationCount,
    retainedWireCount, Fin.addCases_left]
  apply congrArg Sum.inl
  apply Subtype.ext
  exact Internal.sourceRetainedWire_retainedWireIndex _ _ _ _

@[simp] theorem wireOriginEquiv_firstWire
    (result : ParallelSplitResult source wire) :
    result.wireOriginEquiv result.firstWire = Sum.inr (0 : Fin 2) := by
  rw [wireOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.constructionWireEquiv_firstWire]
  simp only [allocationWireOriginEquiv, wireAllocationCount,
    retainedWireCount, Fin.addCases_right]

@[simp] theorem wireOriginEquiv_secondWire
    (result : ParallelSplitResult source wire) :
    result.wireOriginEquiv result.secondWire = Sum.inr (1 : Fin 2) := by
  rw [wireOriginEquiv, Data.Finite.FiniteEquiv.trans_apply,
    result.constructionWireEquiv_secondWire]
  simp only [allocationWireOriginEquiv, wireAllocationCount,
    retainedWireCount, Fin.addCases_right]

def retainedNodeOrigin
    (result : ParallelSplitResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) : result.NodeOrigin :=
  result.nodeOriginEquiv (result.retainedNodeImage node retained)

def firstNodeOrigin
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) : result.NodeOrigin :=
  result.nodeOriginEquiv (result.firstNode site)

def secondNodeOrigin
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) : result.NodeOrigin :=
  result.nodeOriginEquiv (result.secondNode site)

def retainedWireOrigin
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) : result.WireOrigin :=
  result.wireOriginEquiv (result.retainedWireImage sourceWire retained)

def firstWireOrigin
    (result : ParallelSplitResult source wire) : result.WireOrigin :=
  result.wireOriginEquiv result.firstWire

def secondWireOrigin
    (result : ParallelSplitResult source wire) : result.WireOrigin :=
  result.wireOriginEquiv result.secondWire

def targetWireImage
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) : result.checked.val.WireId :=
  result.wireOriginEquiv.symm origin

@[simp] theorem wireOriginEquiv_targetWireImage
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) :
    result.wireOriginEquiv (result.targetWireImage origin) = origin :=
  result.wireOriginEquiv.apply_symm_apply origin

theorem targetWireImage_eq_retainedWireImage
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.targetWireImage
        (result.retainedWireOrigin sourceWire retained) =
      result.retainedWireImage sourceWire retained := by
  exact result.wireOriginEquiv.left_inv _

theorem targetWireImage_first
    (result : ParallelSplitResult source wire) :
    result.targetWireImage result.firstWireOrigin = result.firstWire := by
  exact result.wireOriginEquiv.left_inv _

theorem targetWireImage_second
    (result : ParallelSplitResult source wire) :
    result.targetWireImage result.secondWireOrigin = result.secondWire := by
  exact result.wireOriginEquiv.left_inv _

@[simp] theorem targetWireImage_retained
    (result : ParallelSplitResult source wire)
    (retained : { sourceWire : source.val.WireId //
      sourceWire ∉ result.sourceRemovedWires }) :
    result.targetWireImage (Sum.inl retained) =
      result.retainedWireImage retained.1 retained.2 := by
  calc
    result.targetWireImage (Sum.inl retained) =
        result.targetWireImage
          (result.retainedWireOrigin retained.1 retained.2) := by
            congr 1
            simp [retainedWireOrigin]
    _ = result.retainedWireImage retained.1 retained.2 :=
      result.targetWireImage_eq_retainedWireImage _ _

@[simp] theorem targetWireImage_branch_zero
    (result : ParallelSplitResult source wire) :
    result.targetWireImage (Sum.inr (0 : Fin 2)) = result.firstWire := by
  calc
    result.targetWireImage (Sum.inr (0 : Fin 2)) =
        result.targetWireImage result.firstWireOrigin := by
          congr 1
          simp [firstWireOrigin]
    _ = result.firstWire := result.targetWireImage_first

@[simp] theorem targetWireImage_branch_one
    (result : ParallelSplitResult source wire) :
    result.targetWireImage (Sum.inr (1 : Fin 2)) = result.secondWire := by
  calc
    result.targetWireImage (Sum.inr (1 : Fin 2)) =
        result.targetWireImage result.secondWireOrigin := by
          congr 1
          simp [secondWireOrigin]
    _ = result.secondWire := result.targetWireImage_second

def originSignature
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) : Sig :=
  match origin with
  | .inl retained => (source.val.wires retained.1).sig
  | .inr _ => (source.val.wires wire).sig

def originScope
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) : source.val.RegionId :=
  match origin with
  | .inl retained => (source.val.wires retained.1).scope
  | .inr _ => (source.val.wires wire).scope

theorem targetWireImage_signature
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) :
    (result.checked.val.wires (result.targetWireImage origin)).sig =
      result.originSignature origin := by
  rcases origin with retained | branch
  · rw [result.targetWireImage_retained,
      result.retainedWireImage_signature]
    rfl
  · by_cases first : branch = (0 : Fin 2)
    · subst branch
      rw [result.targetWireImage_branch_zero, result.firstWire_signature]
      rfl
    · have branchExact : branch = (1 : Fin 2) := by
        apply Fin.ext
        omega
      subst branch
      rw [result.targetWireImage_branch_one, result.secondWire_signature]
      rfl

theorem targetWireImage_scopeOrigin
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) :
    result.regionOriginEquiv
        (result.checked.val.wires (result.targetWireImage origin)).scope =
      result.originScope origin := by
  rcases origin with retained | branch
  · rw [result.targetWireImage_retained, result.retainedWireImage_scope,
      result.regionOriginEquiv_targetRegion]
    rfl
  · by_cases first : branch = (0 : Fin 2)
    · subst branch
      rw [result.targetWireImage_branch_zero, result.firstWire_scope,
        result.regionOriginEquiv_targetRegion]
      rfl
    · have branchExact : branch = (1 : Fin 2) := by
        apply Fin.ext
        omega
      subst branch
      rw [result.targetWireImage_branch_one, result.secondWire_scope,
        result.regionOriginEquiv_targetRegion]
      rfl

structure OriginEndpoint
    (result : ParallelSplitResult source wire) where
  node : result.NodeOrigin
  port : CPort
  deriving DecidableEq

def endpointOriginEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      (CEndpoint result.checked.val.nodeCount) (OriginEndpoint result) where
  toFun := fun endpoint =>
    ⟨result.nodeOriginEquiv endpoint.node, endpoint.port⟩
  invFun := fun endpoint =>
    ⟨result.nodeOriginEquiv.symm endpoint.node, endpoint.port⟩
  left_inv := by
    intro endpoint
    cases endpoint with
    | mk node port =>
        exact congrArg (fun value => CEndpoint.mk value port)
          (result.nodeOriginEquiv.left_inv node)
  right_inv := by
    intro endpoint
    cases endpoint with
    | mk node port =>
        exact congrArg (fun value => OriginEndpoint.mk value port)
          (result.nodeOriginEquiv.right_inv node)

def retainedOriginEndpoints
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    List (OriginEndpoint result) :=
  (result.retainedTargetEndpoints sourceWire retained).map
      result.endpointOriginEquiv ++
    (result.targetArgumentEndpoints sourceWire retained).map
      result.endpointOriginEquiv

def firstBranchOriginEndpoints
    (result : ParallelSplitResult source wire) :
    List (OriginEndpoint result) :=
  (Data.Finite.allFin result.sites.sites.length).map fun site =>
    { node := Sum.inr (Sum.inl site), port := .head }

def secondBranchOriginEndpoints
    (result : ParallelSplitResult source wire) :
    List (OriginEndpoint result) :=
  (Data.Finite.allFin result.sites.sites.length).map fun site =>
    { node := Sum.inr (Sum.inr site), port := .head }

/-- Construction-owned endpoint table indexed by neutral wire origins. -/
def originEndpoints
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) : List (OriginEndpoint result) :=
  match origin with
  | .inl retained =>
      result.retainedOriginEndpoints retained.1 retained.2
  | .inr branch =>
      if branch = (0 : Fin 2) then
        result.firstBranchOriginEndpoints
      else
        result.secondBranchOriginEndpoints

/-- Classifying the checked endpoint table produces exactly the independent
construction-owned origin table. -/
theorem classifiedEndpoints_eq_originEndpoints
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) :
    (result.checked.val.wires
        (result.targetWireImage origin)).endpoints.map
          result.endpointOriginEquiv =
      result.originEndpoints origin := by
  rcases origin with retained | branch
  · have targetExact :
        result.targetWireImage (Sum.inl retained) =
          result.retainedWireImage retained.1 retained.2 := by
      calc
        result.targetWireImage (Sum.inl retained) =
            result.targetWireImage
              (result.retainedWireOrigin retained.1 retained.2) := by
                congr 1
                simp [retainedWireOrigin]
        _ = result.retainedWireImage retained.1 retained.2 :=
          result.targetWireImage_eq_retainedWireImage _ _
    rw [targetExact, result.retainedWireImage_endpoints]
    simp only [originEndpoints, retainedOriginEndpoints, List.map_append]
  · by_cases first : branch = (0 : Fin 2)
    · subst branch
      have targetExact :
          result.targetWireImage (Sum.inr (0 : Fin 2)) =
            result.firstWire := by
        calc
          result.targetWireImage (Sum.inr (0 : Fin 2)) =
              result.targetWireImage result.firstWireOrigin := by
                congr 1
                simp [firstWireOrigin]
          _ = result.firstWire := result.targetWireImage_first
      rw [targetExact, result.firstWire_endpoints]
      simp [originEndpoints, firstBranchOriginEndpoints,
        endpointOriginEquiv, Function.comp_def]
    · have branchExact : branch = (1 : Fin 2) := by
        apply Fin.ext
        omega
      subst branch
      have targetExact :
          result.targetWireImage (Sum.inr (1 : Fin 2)) =
            result.secondWire := by
        calc
          result.targetWireImage (Sum.inr (1 : Fin 2)) =
              result.targetWireImage result.secondWireOrigin := by
                congr 1
                simp [secondWireOrigin]
          _ = result.secondWire := result.targetWireImage_second
      rw [targetExact, result.secondWire_endpoints]
      simp [originEndpoints, secondBranchOriginEndpoints,
        endpointOriginEquiv, Function.comp_def]

structure EndpointFiberEquiv
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) where
  equivalence : Data.Finite.FiniteEquiv
    { endpoint // endpoint ∈
      (result.checked.val.wires (result.targetWireImage origin)).endpoints }
    { endpoint // endpoint ∈ result.originEndpoints origin }
  forward_exact : ∀ endpoint,
    (equivalence endpoint).1 = result.endpointOriginEquiv endpoint.1
  inverse_exact : ∀ endpoint,
    (equivalence.symm endpoint).1 =
      result.endpointOriginEquiv.symm endpoint.1

def endpointFiberEquiv
    (result : ParallelSplitResult source wire)
    (origin : result.WireOrigin) : EndpointFiberEquiv result origin where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨result.endpointOriginEquiv endpoint.1, by
          have member : result.endpointOriginEquiv endpoint.1 ∈
              (result.checked.val.wires
                (result.targetWireImage origin)).endpoints.map
                  result.endpointOriginEquiv :=
            List.mem_map.mpr ⟨endpoint.1, endpoint.2, rfl⟩
          rw [result.classifiedEndpoints_eq_originEndpoints] at member
          exact member⟩
      invFun := fun endpoint =>
        ⟨result.endpointOriginEquiv.symm endpoint.1, by
          have member : endpoint.1 ∈
              (result.checked.val.wires
                (result.targetWireImage origin)).endpoints.map
                  result.endpointOriginEquiv := by
            rw [result.classifiedEndpoints_eq_originEndpoints]
            exact endpoint.2
          rcases List.mem_map.mp member with
            ⟨targetEndpoint, targetMember, exact⟩
          have targetExact : targetEndpoint =
              result.endpointOriginEquiv.symm endpoint.1 := by
            apply result.endpointOriginEquiv.injective
            rw [result.endpointOriginEquiv.apply_symm_apply]
            exact exact
          simpa only [targetExact] using targetMember⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact result.endpointOriginEquiv.left_inv endpoint.1
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact result.endpointOriginEquiv.right_inv endpoint.1 }
  forward_exact := by intro; rfl
  inverse_exact := by intro; rfl

end ParallelSplitResult

end ConcreteWirePrimitive

end VisualProof
