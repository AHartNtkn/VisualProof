import VisualProof.Concrete.Operation.Structural.SpawnCore

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

def endpointSubset {nodeCount : Nat}
    (kept available : List (CEndpoint nodeCount)) : Bool :=
  kept.all fun endpoint => decide (endpoint ∈ available)

theorem endpointSubset_eq_true_iff
    {nodeCount : Nat} (kept available : List (CEndpoint nodeCount)) :
    endpointSubset kept available = true ↔
      ∀ endpoint, endpoint ∈ kept → endpoint ∈ available := by
  simp [endpointSubset]

/-- Split a wire's endpoint occurrences between the original identity and one
fresh identity at the same scope. -/
def severWireRaw (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) : Concrete.Diagram where
  regionCount := input.regionCount
  nodeCount := input.nodeCount
  wireCount := input.wireCount + 1
  root := input.root
  regions := input.regions
  nodes := input.nodes
  wires := Fin.lastCases
    { scope := (input.wires wire).scope
      endpoints := (input.wires wire).endpoints.filter
        (fun endpoint => decide (endpoint ∉ keep)) }
    (fun candidate =>
      if candidate = wire then
        { scope := (input.wires wire).scope
          endpoints := (input.wires wire).endpoints.filter
            (fun endpoint => decide (endpoint ∈ keep)) }
      else
        input.wires candidate)

def severWireProvenance (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    WireProvenance input (severWireRaw input wire keep) :=
  WireProvenance.rootFiltered input (severWireRaw input wire keep)
    (fun source => some source.castSucc) (by
      intro left right mapped hleft hright
      change some left.castSucc = some mapped at hleft
      change some right.castSucc = some mapped at hright
      have heq : left.castSucc = right.castSucc :=
        Option.some.inj (hleft.trans hright.symm)
      apply Fin.ext
      exact congrArg (fun value : Fin (input.wireCount + 1) => value.val) heq)

def severWireWireTransport (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (CEndpoint input.nodeCount)) :
    WireTransport input (severWireRaw input wire keep) :=
  WireTransport.append input (severWireRaw input wire keep) 1 rfl

def applyWireSever (orientation : Orientation)
    (input : Checked ) (wire : Fin input.val.wireCount)
    (keep : List (CEndpoint input.val.nodeCount)) :
    Except Error (OperationReceipt input) :=
  if erasurePolarity orientation
      (concreteCutDepth input.val (input.val.wires wire).scope) then
    if endpointSubset keep (input.val.wires wire).endpoints then
      match hcheck : checkWellFormed
          (severWireRaw input.val wire keep) with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (OperationReceipt.ofChecked input
          (severWireRaw input.val wire keep)
          (severWireProvenance input.val wire keep)
          (severWireWireTransport input.val wire keep) result hcheck)
    else
      .error .invalidSelection
  else
    .error .wrongPolarity

theorem applyWireSever_preserves_raw
    (happly : applyWireSever orientation input wire keep = .ok result) :
    result.result.val = severWireRaw input.val wire keep := by
  unfold applyWireSever at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck

theorem applyWireSever_realizes
    (happly : applyWireSever orientation input wire keep = .ok result) :
    result.Realizes (severWireRaw input.val wire keep)
      (severWireProvenance input.val wire keep)
      (severWireWireTransport input.val wire keep) := by
  unfold applyWireSever at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact OperationReceipt.ofChecked_realizes _ _ _ _ checked hcheck

theorem applyWireSever_success (orientation : Orientation) (input : Checked )
    (wire : Fin input.val.wireCount)
    (keep : List (CEndpoint input.val.nodeCount)) (result : OperationReceipt input)
    (happly : applyWireSever orientation input wire keep = .ok result) :
    erasurePolarity orientation
        (concreteCutDepth input.val (input.val.wires wire).scope) ∧
      endpointSubset keep (input.val.wires wire).endpoints ∧
      result.result.val = severWireRaw input.val wire keep := by
  have hpolarity : erasurePolarity orientation
      (concreteCutDepth input.val (input.val.wires wire).scope) := by
    by_cases h : erasurePolarity orientation
        (concreteCutDepth input.val (input.val.wires wire).scope)
    · exact h
    · simp [applyWireSever, h] at happly
  have hsubset : endpointSubset keep (input.val.wires wire).endpoints := by
    by_cases h : endpointSubset keep (input.val.wires wire).endpoints
    · exact h
    · simp [applyWireSever, hpolarity, h] at happly
  exact ⟨hpolarity, hsubset, applyWireSever_preserves_raw happly⟩

def joinWireDomain (input : Concrete.Diagram)
    (inner : Fin input.wireCount) : SurvivorDomain input.wireCount where
  survives candidate := decide (candidate ≠ inner)

/-- Remove the inner wire and append its endpoints to the outer wire. -/
def joinWireRaw (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) : Concrete.Diagram :=
  let domain := joinWireDomain input inner
  { regionCount := input.regionCount
    nodeCount := input.nodeCount
    wireCount := domain.count
    root := input.root
    regions := input.regions
    nodes := input.nodes
    wires := fun candidate =>
      let original := domain.origin candidate
      if original = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else
        input.wires original }

def joinWireProvenance (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) :
    WireProvenance input (joinWireRaw input outer inner) :=
  let domain := joinWireDomain input inner
  WireProvenance.rootFiltered input (joinWireRaw input outer inner)
    domain.index? (by
      exact survivor_index?_injective domain)

/-- Logical wire transport for join. The absorbed identity and the retained
identity intentionally coalesce at the retained wire's dense result index. -/
def joinWireWireTransport (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) :
    WireTransport input (joinWireRaw input outer inner) :=
  let domain := joinWireDomain input inner
  WireTransport.rootFiltered input (joinWireRaw input outer inner)
    (fun wire => if wire = inner then domain.index? outer else domain.index? wire)

theorem joinWireWireTransport_coalesces_pair
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (hne : outer ≠ inner)
    (houter : (input.wires outer).scope = input.root)
    (_hinner : (input.wires inner).scope = input.root) :
    ∃ mapped,
      (joinWireWireTransport input outer inner).transportBoundary
          [outer, inner] = some [mapped, mapped] ∧
        (joinWireProvenance input outer inner).image? inner = none := by
  let domain := joinWireDomain input inner
  have houterSurvives : domain.survives outer = true := by
    simp [domain, joinWireDomain, hne]
  let mapped := domain.index outer houterSurvives
  have houterIndex : domain.index? outer = some mapped := by
    exact domain.index?_index outer houterSurvives
  have hinnerDeleted : domain.index? inner = none := by
    rw [domain.index?_eq_none_iff]
    simp [domain, joinWireDomain]
  have hinnerDeleted' :
      (joinWireDomain input inner).index? inner = none := by
    simpa [domain] using hinnerDeleted
  have horigin : domain.origin mapped = outer := by
    exact domain.origin_index outer houterSurvives
  have hmappedScope :
      ((joinWireRaw input outer inner).wires mapped).scope =
        (joinWireRaw input outer inner).root := by
    change (if domain.origin mapped = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else input.wires (domain.origin mapped)).scope = input.root
    rw [horigin]
    simp [houter]
  have houterImage :
      (joinWireWireTransport input outer inner).image? outer =
        some mapped := by
    unfold joinWireWireTransport WireTransport.rootFiltered
    dsimp only
    rw [if_neg hne, houterIndex]
    change (if ((joinWireRaw input outer inner).wires mapped).scope =
        (joinWireRaw input outer inner).root then some mapped else none) =
      some mapped
    simp [hmappedScope]
  have hinnerImage :
      (joinWireWireTransport input outer inner).image? inner =
        some mapped := by
    unfold joinWireWireTransport WireTransport.rootFiltered
    dsimp only
    rw [if_pos rfl, houterIndex]
    change (if ((joinWireRaw input outer inner).wires mapped).scope =
        (joinWireRaw input outer inner).root then some mapped else none) =
      some mapped
    simp [hmappedScope]
  refine ⟨mapped, ?_, ?_⟩
  · rw [WireTransport.transportBoundary, houterImage,
      WireTransport.transportBoundary, hinnerImage,
      WireTransport.transportBoundary]
    rfl
  · simp [joinWireProvenance, WireProvenance.rootFiltered,
      hinnerDeleted']

def removeWireProvenance (input : Checked )
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection := {}) :
    WireProvenance input.val (input.val.removeRaw selection domains) :=
  WireProvenance.rootFiltered input.val
    (input.val.removeRaw selection domains) domains.wires.index?
    (survivor_index?_injective domains.wires)

def removeWireWireTransport (input : Checked )
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection := {}) :
    WireTransport input.val (input.val.removeRaw selection domains) :=
  WireTransport.survivors input.val
    (input.val.removeRaw selection domains) domains.wires rfl

theorem removeWireWireTransport_image_origin
    (input : Checked )
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (wire : Fin input.val.wireCount)
    (mapped : Fin (input.val.removeRaw selection domains).wireCount)
    (himage : (removeWireWireTransport input selection domains).image? wire =
      some mapped) :
    domains.wires.origin mapped = wire := by
  unfold removeWireWireTransport WireTransport.survivors
    WireTransport.rootFiltered at himage
  dsimp only at himage
  cases hindex : domains.wires.index? wire with
  | none =>
      rw [hindex] at himage
      change (none >>= fun mapped =>
        if ((input.val.removeRaw selection domains).wires mapped).scope =
            (input.val.removeRaw selection domains).root then some mapped else none) =
          some mapped at himage
      contradiction
  | some compact =>
      rw [hindex] at himage
      change (if ((input.val.removeRaw selection domains).wires compact).scope =
          (input.val.removeRaw selection domains).root then some compact else none) =
        some mapped at himage
      by_cases hroot : ((input.val.removeRaw selection domains).wires compact).scope =
          (input.val.removeRaw selection domains).root
      · rw [if_pos hroot] at himage
        have hmapped : compact = mapped := Option.some.inj himage
        subst mapped
        exact (domains.wires.index?_eq_some_iff wire compact).1 hindex
      · rw [if_neg hroot] at himage
        contradiction

/-- Successful removal transport is exactly survivor compaction at every
ordered boundary position.  The equality retains order and duplicates. -/
theorem removeWireWireTransport_boundary_origins
    (input : Checked )
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin (input.val.removeRaw selection domains).wireCount))
    (htransport : (removeWireWireTransport input selection domains).transportBoundary
      boundary = some mapped) :
    mapped.map domains.wires.origin = boundary := by
  have hlength := (removeWireWireTransport input selection domains)
    |>.transportBoundary_length htransport
  apply List.ext_get (by simpa using hlength)
  intro index hmapped hboundary
  rw [List.get_eq_getElem, List.getElem_map]
  let sourceIndex : Fin boundary.length := ⟨index, hboundary⟩
  have himage := (removeWireWireTransport input selection domains)
    |>.transportBoundary_get htransport sourceIndex
  apply removeWireWireTransport_image_origin input selection domains
  simpa [sourceIndex] using himage

def spliceFrameWireProvenance (input : Splice.Input ) :
    WireProvenance input.frame.val input.plugLayout.plugRaw :=
  let layout := input.plugLayout
  let domain := input.wireQuotient
  WireProvenance.rootFiltered input.frame.val layout.plugRaw
    (fun wire => (domain.index? wire).map layout.frameWire) (by
      intro left right mapped hleft hright
      rw [Option.map_eq_some_iff] at hleft hright
      obtain ⟨leftIndex, hleftIndex, hleftMapped⟩ := hleft
      obtain ⟨rightIndex, hrightIndex, hrightMapped⟩ := hright
      have mappedEq : layout.frameWire leftIndex =
          layout.frameWire rightIndex := hleftMapped.trans hrightMapped.symm
      have indexEq : leftIndex = rightIndex := by
        apply Fin.ext
        exact congrArg (fun value : Fin layout.wireCount => value.val) mappedEq
      subst rightIndex
      exact survivor_index?_injective domain hleftIndex hrightIndex)

/-- Logical frame transport for splice. Every original frame identity maps
through its quotient class, including nonrepresentative members that graph
provenance must omit to remain injective. -/
def spliceFrameWireTransport (input : Splice.Input ) :
    WireTransport input.frame.val input.plugLayout.plugRaw :=
  let layout := input.plugLayout
  WireTransport.rootFiltered input.frame.val layout.plugRaw
    (fun wire => some (layout.frameWire (input.quotientWire wire)))

theorem spliceFrameWireTransport_boundary_eq
    (input : Splice.Input )
    (boundary : List (Fin input.frame.val.wireCount))
    (mapped : List (Fin input.plugLayout.plugRaw.wireCount))
    (htransport :
      (spliceFrameWireTransport input).transportBoundary boundary =
        some mapped) :
    mapped =
      boundary.map fun wire =>
        input.plugLayout.frameWire (input.quotientWire wire) := by
  have hlength :=
    (spliceFrameWireTransport input).transportBoundary_length htransport
  have hmapLength :
      (boundary.map fun wire =>
        input.plugLayout.frameWire (input.quotientWire wire)).length =
          boundary.length :=
    List.length_map (as := boundary)
      (fun wire => input.plugLayout.frameWire (input.quotientWire wire))
  apply List.ext_get (hlength.trans hmapLength.symm)
  intro index hmapped hboundary
  have hsource : index < boundary.length := by
    rw [← hmapLength]
    exact hboundary
  let sourceIndex : Fin boundary.length := ⟨index, hsource⟩
  have himage :=
    (spliceFrameWireTransport input).transportBoundary_get htransport
      sourceIndex
  unfold spliceFrameWireTransport WireTransport.rootFiltered at himage
  dsimp only at himage
  change
    (if (input.plugLayout.plugRaw.wires
          (input.plugLayout.frameWire
            (input.quotientWire (boundary.get sourceIndex)))).scope =
        input.plugLayout.plugRaw.root then
      some (input.plugLayout.frameWire
        (input.quotientWire (boundary.get sourceIndex)))
    else none) =
      some (mapped.get (Fin.cast
        ((spliceFrameWireTransport input).transportBoundary_length
          htransport).symm sourceIndex)) at himage
  split at himage
  · have heq := Option.some.inj himage
    change mapped[index] =
      (boundary.map fun wire =>
        input.plugLayout.frameWire (input.quotientWire wire))[index]
    rw [List.getElem_map]
    simpa [sourceIndex] using heq.symm
  · contradiction

def applyWireJoin (orientation : Orientation)
    (input : Checked )
    (first second : Fin input.val.wireCount) :
    Except Error (OperationReceipt input) :=
  if first = second then
    .error .selfWire
  else
    let firstScope := (input.val.wires first).scope
    let secondScope := (input.val.wires second).scope
    if input.val.Encloses firstScope secondScope then
      if spawnPolarity orientation (concreteCutDepth input.val secondScope) then
        match hcheck : checkWellFormed
            (joinWireRaw input.val first second) with
        | .error error => .error (.resultNotWellFormed error)
        | .ok result => .ok (OperationReceipt.ofChecked input
            (joinWireRaw input.val first second)
            (joinWireProvenance input.val first second)
            (joinWireWireTransport input.val first second) result hcheck)
      else
        .error .wrongPolarity
    else if input.val.Encloses secondScope firstScope then
      if spawnPolarity orientation (concreteCutDepth input.val firstScope) then
        match hcheck : checkWellFormed
            (joinWireRaw input.val second first) with
        | .error error => .error (.resultNotWellFormed error)
        | .ok result => .ok (OperationReceipt.ofChecked input
            (joinWireRaw input.val second first)
            (joinWireProvenance input.val second first)
            (joinWireWireTransport input.val second first) result hcheck)
      else
        .error .wrongPolarity
    else
      .error .incomparableScopes

theorem applyWireJoin_success_shape
    (happly : applyWireJoin orientation input first second = .ok result) :
    result.result.val = joinWireRaw input.val first second ∨
      result.result.val = joinWireRaw input.val second first := by
  unfold applyWireJoin at happly
  split at happly <;> try contradiction
  dsimp only at happly
  split at happly
  · split at happly <;> try contradiction
    split at happly <;> try contradiction
    rename_i checked hcheck
    cases happly
    exact Or.inl (checkWellFormed_preserves_input hcheck)
  · split at happly <;> try contradiction
    split at happly <;> try contradiction
    split at happly <;> try contradiction
    rename_i checked hcheck
    cases happly
    exact Or.inr (checkWellFormed_preserves_input hcheck)

theorem applyWireJoin_realizes
    (happly : applyWireJoin orientation input first second = .ok result) :
    result.Realizes (joinWireRaw input.val first second)
        (joinWireProvenance input.val first second)
        (joinWireWireTransport input.val first second) ∨
      result.Realizes (joinWireRaw input.val second first)
        (joinWireProvenance input.val second first)
        (joinWireWireTransport input.val second first) := by
  unfold applyWireJoin at happly
  split at happly <;> try contradiction
  dsimp only at happly
  split at happly
  · split at happly <;> try contradiction
    split at happly <;> try contradiction
    rename_i checked hcheck
    cases happly
    exact Or.inl (OperationReceipt.ofChecked_realizes _ _ _ _ checked hcheck)
  · split at happly <;> try contradiction
    split at happly <;> try contradiction
    split at happly <;> try contradiction
    rename_i checked hcheck
    cases happly
    exact Or.inr (OperationReceipt.ofChecked_realizes _ _ _ _ checked hcheck)

theorem applyWireJoin_success (orientation : Orientation) (input : Checked )
    (first second : Fin input.val.wireCount) (result : OperationReceipt input)
    (happly : applyWireJoin orientation input first second = .ok result) :
    first ≠ second ∧
      ((input.val.Encloses (input.val.wires first).scope
          (input.val.wires second).scope ∧
        spawnPolarity orientation
          (concreteCutDepth input.val (input.val.wires second).scope) ∧
        result.result.val = joinWireRaw input.val first second) ∨
       (input.val.Encloses (input.val.wires second).scope
          (input.val.wires first).scope ∧
        spawnPolarity orientation
          (concreteCutDepth input.val (input.val.wires first).scope) ∧
        result.result.val = joinWireRaw input.val second first)) := by
  unfold applyWireJoin at happly
  split at happly
  · contradiction
  · rename_i hdistinct
    refine ⟨hdistinct, ?_⟩
    dsimp only at happly
    split at happly
    · rename_i hfirst
      split at happly
      · rename_i hpolarity
        split at happly <;> try contradiction
        rename_i checked hcheck
        cases happly
        exact Or.inl ⟨hfirst, hpolarity,
          checkWellFormed_preserves_input hcheck⟩
      · contradiction
    · rename_i hnotFirst
      split at happly
      · rename_i hsecond
        split at happly
        · rename_i hpolarity
          split at happly <;> try contradiction
          rename_i checked hcheck
          cases happly
          exact Or.inr ⟨hsecond, hpolarity,
            checkWellFormed_preserves_input hcheck⟩
        · contradiction
      · contradiction

theorem applyWireJoin_success_realizes
    (orientation : Orientation) (input : Checked )
    (first second : Fin input.val.wireCount)
    (result : OperationReceipt input)
    (happly : applyWireJoin orientation input first second = .ok result) :
    first ≠ second ∧
      ((input.val.Encloses (input.val.wires first).scope
          (input.val.wires second).scope ∧
        spawnPolarity orientation
          (concreteCutDepth input.val (input.val.wires second).scope) ∧
        result.Realizes
          (joinWireRaw input.val first second)
          (joinWireProvenance input.val first second)
          (joinWireWireTransport input.val first second)) ∨
       (input.val.Encloses (input.val.wires second).scope
          (input.val.wires first).scope ∧
        spawnPolarity orientation
          (concreteCutDepth input.val (input.val.wires first).scope) ∧
        result.Realizes
          (joinWireRaw input.val second first)
          (joinWireProvenance input.val second first)
          (joinWireWireTransport input.val second first))) := by
  unfold applyWireJoin at happly
  split at happly
  · contradiction
  · rename_i distinct
    refine ⟨distinct, ?_⟩
    dsimp only at happly
    split at happly
    · rename_i ordered
      split at happly
      · rename_i polarity
        split at happly
        · contradiction
        · rename_i checked checkResult
          cases happly
          exact Or.inl ⟨ordered, polarity,
            OperationReceipt.ofChecked_realizes _ _ _ _ checked checkResult⟩
      · contradiction
    · split at happly
      · rename_i reverseOrdered
        split at happly
        · rename_i polarity
          split at happly
          · contradiction
          · rename_i checked checkResult
            cases happly
            exact Or.inr ⟨reverseOrdered, polarity,
              OperationReceipt.ofChecked_realizes _ _ _ _ checked checkResult⟩
        · contradiction
      · contradiction

def liftCRegion {regionCount : Nat} (added : Nat) :
    CRegion regionCount → CRegion (regionCount + added)
  | .sheet => .sheet
  | .cut parent => .cut (Fin.castAdd added parent)
  | .bubble parent arity => .bubble (Fin.castAdd added parent) arity

def reparentLiftedRegion {regionCount : Nat} (added : Nat)
    (parent : Fin (regionCount + added)) :
    CRegion regionCount → CRegion (regionCount + added)
  | .sheet => .sheet
  | .cut _ => .cut parent
  | .bubble _ arity => .bubble parent arity

def liftCNode {regionCount : Nat} (added : Nat) :
    CNode regionCount → CNode (regionCount + added)
  | .identity region arity =>
      .identity (Fin.castAdd added region) arity
  | .atom region binder =>
      .atom (Fin.castAdd added region) (Fin.castAdd added binder)
def reparentLiftedNode {regionCount : Nat} (added : Nat)
    (region : Fin (regionCount + added)) :
    CNode regionCount → CNode (regionCount + added)
  | .identity _ arity => .identity region arity
  | .atom _ binder => .atom region (Fin.castAdd added binder)
def liftCWireRegions {regionCount nodeCount : Nat} (added : Nat) :
    CWire regionCount nodeCount → CWire (regionCount + added) nodeCount
  | wire =>
      { scope := Fin.castAdd added wire.scope, endpoints := wire.endpoints }

end VisualProof.Concrete
