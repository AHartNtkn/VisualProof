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

private theorem insertEverywhere_append
    (value : α) (pre suffix : List α) :
    pre ++ value :: suffix ∈
      insertEverywhere value (pre ++ suffix) := by
  induction pre with
  | nil =>
      cases suffix <;> simp [insertEverywhere]
  | cons head tail induction =>
      simp [insertEverywhere, induction]

private theorem mem_rawPermutations [DecidableEq α]
    {source target : List α}
    (sourceNodup : source.Nodup)
    (targetNodup : target.Nodup)
    (same : ∀ value, value ∈ source ↔ value ∈ target) :
    target ∈ rawPermutations source := by
  induction source generalizing target with
  | nil =>
      have targetEmpty : target = [] := by
        cases target with
        | nil => rfl
        | cons head tail =>
            have : head ∈ ([] : List α) :=
              (same head).mpr (by simp)
            contradiction
      subst target
      simp [rawPermutations]
  | cons head tail induction =>
      have headMember : head ∈ target :=
        (same head).mp (by simp)
      obtain ⟨pre, suffix, targetExact⟩ :=
        List.append_of_mem headMember
      subst target
      have headNotTail : head ∉ tail :=
        (List.nodup_cons.mp sourceNodup).1
      have targetParts := List.nodup_append.mp targetNodup
      have headNotPre : head ∉ pre := by
        intro member
        exact targetParts.2.2 head member head (by simp) rfl
      have headNotSuffix : head ∉ suffix :=
        (List.nodup_cons.mp targetParts.2.1).1
      have restNodup : (pre ++ suffix).Nodup := by
        apply List.Sublist.nodup _ targetNodup
        exact List.Sublist.append (List.Sublist.refl pre)
          ((List.Sublist.refl suffix).cons head)
      have restSame : ∀ value, value ∈ tail ↔
          value ∈ pre ++ suffix := by
        intro value
        constructor
        · intro member
          have inTarget : value ∈ pre ++ head :: suffix :=
            (same value).mp (by simp [member])
          rw [List.mem_append] at inTarget ⊢
          rcases inTarget with inPre | inHead
          · exact Or.inl inPre
          · simp only [List.mem_cons] at inHead
            rcases inHead with exact | inSuffix
            · subst value; contradiction
            · exact Or.inr inSuffix
        · intro member
          have inTarget : value ∈ pre ++ head :: suffix := by
            rw [List.mem_append] at member ⊢
            rcases member with inPre | inSuffix
            · exact Or.inl inPre
            · exact Or.inr (by simp [inSuffix])
          have inSource := (same value).mpr inTarget
          simp only [List.mem_cons] at inSource
          rcases inSource with exact | inTail
          · subst value
            rw [List.mem_append] at member
            rcases member with inPre | inSuffix <;> contradiction
          · exact inTail
      have restMember :=
        induction (List.nodup_cons.mp sourceNodup).2 restNodup restSame
      simp only [rawPermutations, List.mem_flatMap]
      exact ⟨pre ++ suffix, restMember,
        insertEverywhere_append head pre suffix⟩

private theorem move_to_front
    (value : α) (pre suffix : List α) :
    (value :: pre ++ suffix).Perm
      (pre ++ value :: suffix) := by
  induction pre with
  | nil => simp
  | cons head tail induction =>
      exact
        (List.Perm.swap value head (tail ++ suffix)).symm.trans
          (List.Perm.cons head induction)

private theorem perm_of_nodup_same_membership [DecidableEq α]
    {left right : List α}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (same : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons head tail =>
          have : head ∈ ([] : List α) :=
            (same head).mpr (by simp)
          contradiction
  | cons head tail induction =>
      have headMember : head ∈ right :=
        (same head).mp (by simp)
      obtain ⟨pre, suffix, rightExact⟩ :=
        List.append_of_mem headMember
      subst right
      have headNotTail : head ∉ tail :=
        (List.nodup_cons.mp leftNodup).1
      have rightParts := List.nodup_append.mp rightNodup
      have headNotPre : head ∉ pre := by
        intro member
        exact rightParts.2.2 head member head (by simp) rfl
      have headNotSuffix : head ∉ suffix :=
        (List.nodup_cons.mp rightParts.2.1).1
      have tailNodup : tail.Nodup :=
        (List.nodup_cons.mp leftNodup).2
      have restNodup : (pre ++ suffix).Nodup := by
        apply List.Sublist.nodup _ rightNodup
        exact List.Sublist.append (List.Sublist.refl pre)
          ((List.Sublist.refl suffix).cons head)
      have restSame : ∀ value, value ∈ tail ↔
          value ∈ pre ++ suffix := by
        intro value
        constructor
        · intro member
          have inRight : value ∈ pre ++ head :: suffix :=
            (same value).mp (by simp [member])
          rw [List.mem_append] at inRight ⊢
          rcases inRight with inPre | inHead
          · exact Or.inl inPre
          · simp only [List.mem_cons] at inHead
            rcases inHead with exact | inSuffix
            · subst value; contradiction
            · exact Or.inr inSuffix
        · intro member
          have inRight : value ∈ pre ++ head :: suffix := by
            rw [List.mem_append] at member ⊢
            rcases member with inPre | inSuffix
            · exact Or.inl inPre
            · exact Or.inr (by simp [inSuffix])
          have inLeft := (same value).mpr inRight
          simp only [List.mem_cons] at inLeft
          rcases inLeft with exact | inTail
          · subst value
            rw [List.mem_append] at member
            rcases member with inPre | inSuffix <;> contradiction
          · exact inTail
      have restPerm : tail.Perm (pre ++ suffix) :=
        induction tailNodup restNodup restSame
      exact
        (List.Perm.cons head restPerm).trans
          (move_to_front head pre suffix)

private def equivPermutation
    (equivalence : FiniteEquiv (Fin left) (Fin right)) :
    FinPermutation right where
  values := (allFin left).map equivalence
  perm := by
    apply perm_of_nodup_same_membership
    · exact
        List.Pairwise.map equivalence
          (fun first second different same =>
            different (equivalence.injective same))
          (allFin_nodup left)
    · exact allFin_nodup right
    · intro value
      constructor
      · intro member
        exact mem_allFin value
      · intro member
        exact List.mem_map.mpr
          ⟨equivalence.invFun value, mem_allFin _,
            equivalence.right_inv value⟩

private theorem equivPermutation_apply
    (equivalence : FiniteEquiv (Fin left) (Fin right))
    (same : left = right)
    (index : Fin left) :
    (equivPermutation equivalence).toEquiv (Fin.cast same index) =
      equivalence index := by
  apply Fin.ext
  simp [equivPermutation, FinPermutation.toEquiv, allFin_eq_finRange]

private theorem equivPermutation_mem
    (equivalence : FiniteEquiv (Fin left) (Fin right)) :
    equivPermutation equivalence ∈ finPermutations right := by
  unfold finPermutations
  simp only [List.mem_filterMap]
  refine ⟨(equivPermutation equivalence).values, ?_, ?_⟩
  · apply mem_rawPermutations
    · exact allFin_nodup right
    · exact (equivPermutation equivalence).nodup
    · intro value
      exact (equivPermutation equivalence).perm.mem_iff.symm
  · rw [dif_pos (equivPermutation equivalence).perm]

private theorem findSome?_isSome_of_mem
    (function : α → Option β)
    (values : List α)
    (value : α)
    (member : value ∈ values)
    (accepted : (function value).isSome = true) :
    (values.findSome? function).isSome = true := by
  induction values with
  | nil => contradiction
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      unfold List.findSome?
      cases headAccepted : function head with
      | none =>
          rcases member with exact | member
          · subst head
            simp [headAccepted] at accepted
          · exact induction member
      | some result => rfl

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

private theorem portCorresponds_true_of
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame)
    (endpoint : CEndpoint left.nodeCount)
    (targetEndpoint : CEndpoint right.nodeCount)
    (corresponds :
      PortCorresponds left right candidate.nodeEquiv endpoint
        targetEndpoint) :
    portCorresponds candidate endpoint targetEndpoint = true := by
  rcases endpoint with ⟨endpointNode, endpointPort⟩
  rcases targetEndpoint with ⟨targetNode, targetPort⟩
  unfold PortCorresponds at corresponds
  rcases corresponds with ⟨nodeExact, rest⟩
  change targetNode = candidate.nodeEquiv endpointNode at nodeExact
  subst targetNode
  unfold portCorresponds
  simp only [decide_true, Bool.true_and]
  cases leftNode : left.nodes endpointNode <;>
    cases rightNode : right.nodes (candidate.nodeEquiv endpointNode)
  all_goals rw [leftNode, rightNode] at rest
  all_goals simp only at rest ⊢
  all_goals try exact decide_eq_true rest
  rename_i leftRegion leftSig leftArity rightRegion rightSig rightArity
  rcases rest with
    ⟨sigExact, arityExact, leftIndex, rightIndex, leftPort, rightPort⟩
  subst endpointPort
  subst targetPort
  simp [identityPorts, sigExact, arityExact]

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
  (ConcreteIso.checkEquivs? left right candidate.regionEquiv
    candidate.nodeEquiv candidate.wireEquiv).isSome

private def toIso
    (candidate :
      ConcreteIsoCandidate left right regionsSame nodesSame wiresSame)
    (accepted : candidate.valid = true) :
    ConcreteIso left right :=
  (ConcreteIso.checkEquivs? left right candidate.regionEquiv
    candidate.nodeEquiv candidate.wireEquiv).get
      (by simpa [valid] using accepted)

private theorem equivCandidate_valid
    (iso : ConcreteIso left right)
    (canonical :
      (ConcreteIso.checkEquivs? left right iso.regions iso.nodes
        iso.wires).isSome = true) :
    let candidate :
        ConcreteIsoCandidate left right iso.regionCount_eq iso.nodeCount_eq
          iso.wireCount_eq :=
      ⟨equivPermutation iso.regions, equivPermutation iso.nodes,
        equivPermutation iso.wires⟩
    candidate.valid = true := by
  let candidate :
      ConcreteIsoCandidate left right iso.regionCount_eq iso.nodeCount_eq
        iso.wireCount_eq :=
    ⟨equivPermutation iso.regions, equivPermutation iso.nodes,
      equivPermutation iso.wires⟩
  have regionsExact : candidate.regionEquiv = iso.regions := by
    apply FiniteEquiv.ext
    intro region
    exact equivPermutation_apply iso.regions iso.regionCount_eq region
  have nodesExact : candidate.nodeEquiv = iso.nodes := by
    apply FiniteEquiv.ext
    intro node
    exact equivPermutation_apply iso.nodes iso.nodeCount_eq node
  have wiresExact : candidate.wireEquiv = iso.wires := by
    apply FiniteEquiv.ext
    intro wire
    exact equivPermutation_apply iso.wires iso.wireCount_eq wire
  change candidate.valid = true
  simpa [valid, regionsExact, nodesExact, wiresExact] using canonical

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

/-- Every deterministic canonical correspondence is discoverable by the
finite identifier search. -/
theorem findConcreteIso?_complete_of_canonical
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (canonical :
      (ConcreteIso.checkEquivs? left right iso.regions iso.nodes
        iso.wires).isSome = true) :
    ∃ found, findConcreteIso? left right = some found := by
  unfold findConcreteIso?
  rw [dif_pos iso.regionCount_eq, dif_pos iso.nodeCount_eq,
    dif_pos iso.wireCount_eq]
  apply Option.isSome_iff_exists.mp
  apply findSome?_isSome_of_mem
    (fun regions =>
      (finPermutations right.nodeCount).findSome? fun nodes =>
        (finPermutations right.wireCount).findSome? fun wires =>
          let candidate :
              ConcreteIsoCandidate left right iso.regionCount_eq
                iso.nodeCount_eq iso.wireCount_eq :=
            ⟨regions, nodes, wires⟩
          if accepted : candidate.valid then
            some (candidate.toIso accepted)
          else none)
    (finPermutations right.regionCount)
    (equivPermutation iso.regions)
    (equivPermutation_mem iso.regions)
  apply findSome?_isSome_of_mem
    (fun nodes =>
      (finPermutations right.wireCount).findSome? fun wires =>
        let candidate :
            ConcreteIsoCandidate left right iso.regionCount_eq
              iso.nodeCount_eq iso.wireCount_eq :=
          ⟨equivPermutation iso.regions, nodes, wires⟩
        if accepted : candidate.valid then
          some (candidate.toIso accepted)
        else none)
    (finPermutations right.nodeCount)
    (equivPermutation iso.nodes)
    (equivPermutation_mem iso.nodes)
  apply findSome?_isSome_of_mem
    (fun wires =>
      let candidate :
          ConcreteIsoCandidate left right iso.regionCount_eq iso.nodeCount_eq
            iso.wireCount_eq :=
        ⟨equivPermutation iso.regions, equivPermutation iso.nodes, wires⟩
      if accepted : candidate.valid then
        some (candidate.toIso accepted)
      else none)
    (finPermutations right.wireCount)
    (equivPermutation iso.wires)
    (equivPermutation_mem iso.wires)
  rw [dif_pos (ConcreteIsoCandidate.equivCandidate_valid iso canonical)]
  rfl

end ConcreteIsoSearch

end VisualProof
