import VisualProof.Diagram.Concrete.Isomorphism
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

namespace ConcreteIsoSearch

open Data.Finite

/-- One executable permutation of a finite identifier space. -/
structure FinPermutation (n : Nat) where
  values : List (Fin n)
  perm : values.Perm (allFin n)

namespace FinPermutation

theorem length (permutation : FinPermutation n) :
    permutation.values.length = n := by
  rw [permutation.perm.length_eq, allFin_eq_finRange,
    List.length_finRange]

theorem nodup (permutation : FinPermutation n) :
    permutation.values.Nodup :=
  permutation.perm.nodup_iff.mpr (allFin_nodup n)

theorem mem (permutation : FinPermutation n) (value : Fin n) :
    value ∈ permutation.values :=
  permutation.perm.mem_iff.mpr (mem_allFin value)

def toEquiv (permutation : FinPermutation n) :
    FiniteEquiv (Fin n) (Fin n) where
  toFun := fun index =>
    permutation.values.get (Fin.cast permutation.length.symm index)
  invFun := fun value =>
    Fin.cast permutation.length
      (DenseList.index permutation.values value (permutation.mem value))
  left_inv := by
    intro index
    apply Fin.ext
    rw [DenseList.index_get permutation.values permutation.nodup
      (Fin.cast permutation.length.symm index)]
    rfl
  right_inv := by
    intro value
    change
      permutation.values.get
          (Fin.cast permutation.length.symm
            (Fin.cast permutation.length
              (DenseList.index permutation.values value
                (permutation.mem value)))) =
        value
    have castRoundtrip :
        Fin.cast permutation.length.symm
            (Fin.cast permutation.length
              (DenseList.index permutation.values value
                (permutation.mem value))) =
          DenseList.index permutation.values value
            (permutation.mem value) := by
      apply Fin.ext
      rfl
    rw [castRoundtrip, DenseList.get_index]

end FinPermutation

private def finCastEquiv {left right : Nat} (same : left = right) :
    FiniteEquiv (Fin left) (Fin right) where
  toFun := Fin.cast same
  invFun := Fin.cast same.symm
  left_inv := by intro value; apply Fin.ext; rfl
  right_inv := by intro value; apply Fin.ext; rfl

private def insertEverywhere (value : α) : List α → List (List α)
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
        (insertEverywhere value tail).map (head :: ·)

private def rawPermutations : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      (rawPermutations tail).flatMap (insertEverywhere head)

private def finPermutations (n : Nat) : List (FinPermutation n) :=
  (rawPermutations (allFin n)).filterMap fun values =>
    if perm : values.Perm (allFin n) then
      some ⟨values, perm⟩
    else
      none

/-- Candidate identifier transport checked before it becomes an isomorphism. -/
private structure ConcreteIsoCandidate
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length)
    (regionsSame : left.regionCount = right.regionCount)
    (nodesSame : left.nodeCount = right.nodeCount)
    (wiresSame : left.wireCount = right.wireCount) where
  regionPermutation : FinPermutation right.regionCount
  nodePermutation : FinPermutation right.nodeCount
  wirePermutation : FinPermutation right.wireCount

namespace ConcreteIsoCandidate

private def regionEquiv
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    FiniteEquiv left.RegionId right.RegionId :=
  (finCastEquiv regionsSame).trans candidate.regionPermutation.toEquiv

private def nodeEquiv
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    FiniteEquiv left.NodeId right.NodeId :=
  (finCastEquiv nodesSame).trans candidate.nodePermutation.toEquiv

private def wireEquiv
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    FiniteEquiv left.WireId right.WireId :=
  (finCastEquiv wiresSame).trans candidate.wirePermutation.toEquiv

private def identityPorts (left right : CPort) : Bool :=
  match left, right with
  | .identity _, .identity _ => true
  | _, _ => false

private theorem identityPorts_of_true
    (left right : CPort)
    (accepted : identityPorts left right = true) :
    ∃ leftIndex rightIndex,
      left = .identity leftIndex ∧ right = .identity rightIndex := by
  cases left <;> cases right <;> simp [identityPorts] at accepted ⊢

private def portCorresponds
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame)
    (endpoint : CEndpoint left.nodeCount)
    (targetEndpoint : CEndpoint right.nodeCount) : Bool :=
  decide (targetEndpoint.node = candidate.nodeEquiv endpoint.node) &&
    match left.nodes endpoint.node, right.nodes targetEndpoint.node with
    | .identity _ leftSig leftArity, .identity _ rightSig rightArity =>
        decide (leftSig = rightSig) &&
          decide (leftArity = rightArity) &&
          identityPorts endpoint.port targetEndpoint.port
    | _, _ => decide (targetEndpoint.port = endpoint.port)

private theorem portCorresponds_of_true
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame)
    (endpoint : CEndpoint left.nodeCount)
    (targetEndpoint : CEndpoint right.nodeCount)
    (accepted :
      portCorresponds candidate endpoint targetEndpoint = true) :
    PortCorresponds left right candidate.nodeEquiv endpoint
      targetEndpoint := by
  rcases endpoint with ⟨endpointNode, endpointPort⟩
  rcases targetEndpoint with ⟨targetNode, targetPort⟩
  unfold portCorresponds at accepted
  rcases Bool.and_eq_true_iff.mp accepted with ⟨nodeExact, rest⟩
  refine ⟨of_decide_eq_true nodeExact, ?_⟩
  cases leftNodeEq : left.nodes endpointNode <;>
    cases rightNodeEq : right.nodes targetNode
  all_goals rw [leftNodeEq, rightNodeEq] at rest
  all_goals simp only at rest ⊢
  all_goals try exact of_decide_eq_true rest
  rename_i leftRegion leftSig leftArity rightRegion rightSig rightArity
  rcases Bool.and_eq_true_iff.mp rest with
    ⟨sigAndArity, ports⟩
  rcases Bool.and_eq_true_iff.mp sigAndArity with
    ⟨sigExact, arityExact⟩
  obtain ⟨leftIndex, rightIndex, leftPort, rightPort⟩ :=
    identityPorts_of_true endpointPort targetPort ports
  exact
    ⟨of_decide_eq_true sigExact, of_decide_eq_true arityExact,
      leftIndex, rightIndex, leftPort, rightPort⟩

private def rootValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  decide (candidate.regionEquiv left.root = right.root)

private def regionsValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  (allFin left.regionCount).all fun region =>
    decide (
      right.regions (candidate.regionEquiv region) =
        (left.regions region).rename candidate.regionEquiv)

private def nodesValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  (allFin left.nodeCount).all fun node =>
    decide (
      right.nodes (candidate.nodeEquiv node) =
        (left.nodes node).rename candidate.regionEquiv)

private def signaturesValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  (allFin left.wireCount).all fun wire =>
    decide (
      (right.wires (candidate.wireEquiv wire)).sig =
        (left.wires wire).sig)

private def scopesValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  (allFin left.wireCount).all fun wire =>
    decide (
      (right.wires (candidate.wireEquiv wire)).scope =
        candidate.regionEquiv (left.wires wire).scope)

private def forwardValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  (allFin left.wireCount).all fun wire =>
    (left.wires wire).endpoints.all fun endpoint =>
      (right.wires (candidate.wireEquiv wire)).endpoints.any
        (portCorresponds candidate endpoint)

private def backwardValid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  (allFin left.wireCount).all fun wire =>
    (right.wires (candidate.wireEquiv wire)).endpoints.all
      (fun targetEndpoint =>
        (left.wires wire).endpoints.any
          (fun endpoint =>
            portCorresponds candidate endpoint targetEndpoint))

private def valid
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame) :
    Bool :=
  rootValid candidate &&
    (regionsValid candidate &&
      (nodesValid candidate &&
        (signaturesValid candidate &&
          (scopesValid candidate &&
            (forwardValid candidate && backwardValid candidate)))))

private def toIso
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame)
    (accepted : candidate.valid = true) :
    ConcreteIso left right where
  regions := candidate.regionEquiv
  nodes := candidate.nodeEquiv
  wires := candidate.wireEquiv
  root := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).1
  region_table := by
    intro region
    have regions :=
      Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp accepted).2 |>.1
    exact of_decide_eq_true
      (List.all_eq_true.mp regions region (mem_allFin region))
  node_table := by
    intro node
    have parts := Bool.and_eq_true_iff.mp accepted |>.2
    have nodes :=
      Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp parts).2 |>.1
    exact of_decide_eq_true
      (List.all_eq_true.mp nodes node (mem_allFin node))
  wire_signature := by
    intro wire
    have parts := Bool.and_eq_true_iff.mp accepted |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have signatures :=
      Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp parts).2 |>.1
    exact of_decide_eq_true
      (List.all_eq_true.mp signatures wire (mem_allFin wire))
  wire_scope := by
    intro wire
    have parts := Bool.and_eq_true_iff.mp accepted |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have scopes :=
      Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp parts).2 |>.1
    exact of_decide_eq_true
      (List.all_eq_true.mp scopes wire (mem_allFin wire))
  endpoint_forward := by
    intro wire endpoint member
    have parts := Bool.and_eq_true_iff.mp accepted |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have endpoints :=
      Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp parts).2 |>.1
    have wireAccepted :=
      List.all_eq_true.mp endpoints wire (mem_allFin wire)
    have endpointAccepted :=
      List.all_eq_true.mp wireAccepted endpoint member
    obtain ⟨targetEndpoint, targetMember, corresponds⟩ :=
      List.any_eq_true.mp endpointAccepted
    exact
      ⟨targetEndpoint, targetMember,
        portCorresponds_of_true candidate endpoint targetEndpoint
          corresponds⟩
  endpoint_backward := by
    intro wire targetEndpoint member
    have parts := Bool.and_eq_true_iff.mp accepted |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have parts := Bool.and_eq_true_iff.mp parts |>.2
    have backwards :=
      Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp parts).2 |>.2
    have wireAccepted :=
      List.all_eq_true.mp backwards wire (mem_allFin wire)
    have endpointAccepted :=
      List.all_eq_true.mp wireAccepted targetEndpoint member
    obtain ⟨endpoint, endpointMember, corresponds⟩ :=
      List.any_eq_true.mp endpointAccepted
    exact
      ⟨endpoint, endpointMember,
        portCorresponds_of_true candidate endpoint targetEndpoint
          corresponds⟩

end ConcreteIsoCandidate

/--
Search every finite identifier transport and return an isomorphism only after
all region, node, wire, scope, signature, and endpoint obligations are proved.
-/
def findConcreteIso?
    {definitions : List (List Sig)}
    (left right : ConcreteDiagram definitions.length) :
    Option (ConcreteIso left right) := by
  if regionsSame : left.regionCount = right.regionCount then
    if nodesSame : left.nodeCount = right.nodeCount then
      if wiresSame : left.wireCount = right.wireCount then
        exact
          (finPermutations right.regionCount).findSome? fun regions =>
            (finPermutations right.nodeCount).findSome? fun nodes =>
              (finPermutations right.wireCount).findSome? fun wires =>
                let candidate :
                    ConcreteIsoCandidate left right regionsSame nodesSame
                      wiresSame :=
                  ⟨regions, nodes, wires⟩
                if accepted : candidate.valid then
                  some (candidate.toIso accepted)
                else
                  none
      else
        exact none
    else
      exact none
  else
    exact none

end ConcreteIsoSearch

end VisualProof
