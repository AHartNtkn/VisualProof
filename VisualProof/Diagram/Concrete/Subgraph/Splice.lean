import VisualProof.Diagram.Concrete.Subgraph.Decomposition

namespace VisualProof.Data.Finite.FinitePartition

open VisualProof.Diagram

/-- The stable dense carrier of normalized partition representatives. -/
def quotientDomain (partition : FinitePartition size) : SurvivorDomain size where
  survives index := decide (partition.representative index = index)

@[simp] theorem quotientDomain_survives_iff
    (partition : FinitePartition size)
    (index : Fin size) :
    partition.quotientDomain.survives index = true ↔
      partition.representative index = index := by
  simp [quotientDomain]

/-- The dense quotient class of an original finite identifier. -/
def classIndex (partition : FinitePartition size)
    (normalized : partition.Normalized) (index : Fin size) :
    partition.quotientDomain.Carrier :=
  partition.quotientDomain.index
    (partition.representative index) (by
      rw [quotientDomain_survives_iff]
      exact normalized index)

@[simp] theorem quotientOrigin_classIndex
    (partition : FinitePartition size) (normalized : partition.Normalized)
    (index : Fin size) :
    partition.quotientDomain.origin
        (partition.classIndex normalized index) =
      partition.representative index := by
  exact SurvivorDomain.origin_index _ _ _

theorem classIndex_eq_iff_related
    (partition : FinitePartition size) (normalized : partition.Normalized)
    (left right : Fin size) :
    partition.classIndex normalized left =
        partition.classIndex normalized right ↔
      partition.related left right = true := by
  constructor
  · intro heq
    apply (related_eq_true_iff partition left right).2
    have horigin := congrArg
      partition.quotientDomain.origin heq
    simpa only [quotientOrigin_classIndex] using horigin
  · intro hrelated
    apply partition.quotientDomain.origin_injective
    simp only [quotientOrigin_classIndex]
    exact (related_eq_true_iff partition left right).1 hrelated

theorem classIndex_surjective
    (partition : FinitePartition size) (normalized : partition.Normalized) :
    Function.Surjective (partition.classIndex normalized) := by
  intro quotient
  refine ⟨partition.quotientDomain.origin quotient, ?_⟩
  apply partition.quotientDomain.origin_injective
  rw [quotientOrigin_classIndex]
  have hsurvives :=
    partition.quotientDomain.origin_survives quotient
  exact (quotientDomain_survives_iff partition _).1 hsurvives

end VisualProof.Data.Finite.FinitePartition

namespace VisualProof.Diagram

open VisualProof.Data.Finite

namespace Splice

/-- Proof-free inputs to checked concrete replacement. -/
structure Input (signature : List Nat) where
  frame : CheckedDiagram signature
  pattern : CheckedOpenDiagram signature
  site : Fin frame.val.regionCount
  attachment : Fin pattern.val.boundary.length → Fin frame.val.wireCount
  binderSpine : BinderSpine pattern.val.diagram
  terminalBody : binderSpine.TerminalBodyContract pattern.val
  binderTarget : Fin binderSpine.proxyCount → Fin frame.val.regionCount

namespace Input

/-- Boundary-position equations; equal pattern-wire identities alone generate them. -/
def attachmentEdges (input : Input signature) :
    List (Fin input.frame.val.wireCount × Fin input.frame.val.wireCount) :=
  (allFin input.pattern.val.boundary.length).flatMap fun left =>
    (allFin input.pattern.val.boundary.length).filterMap fun right =>
      if input.pattern.val.boundary.get left =
          input.pattern.val.boundary.get right then
        some (input.attachment left, input.attachment right)
      else
        none

theorem mem_attachmentEdges_iff (input : Input signature)
    (edge : Fin input.frame.val.wireCount × Fin input.frame.val.wireCount) :
    edge ∈ input.attachmentEdges ↔
      ∃ left right : Fin input.pattern.val.boundary.length,
        input.pattern.val.boundary.get left =
            input.pattern.val.boundary.get right ∧
          edge = (input.attachment left, input.attachment right) := by
  simp only [attachmentEdges, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨left, _, right, _, hright⟩
    split at hright
    · cases hright
      exact ⟨left, right, ‹_›, rfl⟩
    · contradiction
  · rintro ⟨left, right, hwire, rfl⟩
    refine ⟨left, mem_allFin left, right, mem_allFin right, ?_⟩
    rw [if_pos (by
      simpa only [List.get_eq_getElem] using hwire)]

def attachmentPartition (input : Input signature) :
    FinitePartition input.frame.val.wireCount :=
  FinitePartition.ofEdges input.attachmentEdges

theorem attachmentPartition_normalized (input : Input signature) :
    input.attachmentPartition.Normalized :=
  FinitePartition.ofEdges_normalized input.attachmentEdges

def wireQuotient (input : Input signature) :
    SurvivorDomain input.frame.val.wireCount :=
  input.attachmentPartition.quotientDomain

def quotientWire (input : Input signature)
    (wire : Fin input.frame.val.wireCount) : input.wireQuotient.Carrier :=
  input.attachmentPartition.classIndex
    input.attachmentPartition_normalized wire

theorem quotientWire_eq_iff (input : Input signature)
    (left right : Fin input.frame.val.wireCount) :
    input.quotientWire left = input.quotientWire right ↔
      input.attachmentPartition.related left right = true :=
  input.attachmentPartition.classIndex_eq_iff_related
    input.attachmentPartition_normalized left right

theorem equalBoundary_quotientWire_eq (input : Input signature)
    (left right : Fin input.pattern.val.boundary.length)
    (hequal : input.pattern.val.boundary.get left =
      input.pattern.val.boundary.get right) :
    input.quotientWire (input.attachment left) =
      input.quotientWire (input.attachment right) := by
  rw [input.quotientWire_eq_iff]
  exact FinitePartition.generator_related (edges := input.attachmentEdges)
    (edge := (input.attachment left, input.attachment right))
    ((input.mem_attachmentEdges_iff _).2 ⟨left, right, hequal, rfl⟩)

def AttachmentsVisible (input : Input signature) : Prop :=
  ∀ position,
    input.frame.val.Encloses
      (input.frame.val.wires (input.attachment position)).scope input.site

def BinderTargetsInjective (input : Input signature) : Prop :=
  Function.Injective input.binderTarget

def BinderTargetsMatch (input : Input signature) : Prop :=
  ∀ index, ∃ parent,
    input.frame.val.regions (input.binderTarget index) =
      .bubble parent (input.binderSpine.arity index)

def BinderTargetsEnclose (input : Input signature) : Prop :=
  ∀ index, input.frame.val.Encloses (input.binderTarget index) input.site

structure Admissible (input : Input signature) : Prop where
  attachments_visible : input.AttachmentsVisible
  binder_targets_injective : input.BinderTargetsInjective
  binder_targets_match : input.BinderTargetsMatch
  binder_targets_enclose : input.BinderTargetsEnclose

instance (input : Input signature) : Decidable input.AttachmentsVisible := by
  unfold AttachmentsVisible
  exact @Nat.decidableForallFin _ _ fun _ => inferInstance

instance (input : Input signature) : Decidable input.BinderTargetsInjective := by
  unfold BinderTargetsInjective Function.Injective
  exact @Nat.decidableForallFin _ _ fun _ =>
    @Nat.decidableForallFin _ _ fun _ => inferInstance

instance (input : Input signature) : Decidable input.BinderTargetsMatch := by
  unfold BinderTargetsMatch
  exact @Nat.decidableForallFin _ _ fun _ =>
    @Nat.decidableExistsFin _ _ fun _ => inferInstance

instance (input : Input signature) : Decidable input.BinderTargetsEnclose := by
  unfold BinderTargetsEnclose
  exact @Nat.decidableForallFin _ _ fun _ => inferInstance

instance (input : Input signature) : Decidable input.Admissible := by
  by_cases hvisible : input.AttachmentsVisible
  · by_cases hinjective : input.BinderTargetsInjective
    · by_cases hmatch : input.BinderTargetsMatch
      · by_cases henclose : input.BinderTargetsEnclose
        · exact isTrue {
            attachments_visible := hvisible
            binder_targets_injective := hinjective
            binder_targets_match := hmatch
            binder_targets_enclose := henclose
          }
        · exact isFalse fun hadmissible =>
            henclose hadmissible.binder_targets_enclose
      · exact isFalse fun hadmissible =>
          hmatch hadmissible.binder_targets_match
    · exact isFalse fun hadmissible =>
        hinjective hadmissible.binder_targets_injective
  · exact isFalse fun hadmissible =>
      hvisible hadmissible.attachments_visible

inductive Error
  | attachmentNotVisible
  | duplicateBinderTarget
  | binderKindOrArityMismatch
  | binderDoesNotEncloseSite
  | resultNotWellFormed (error : WFError)
  deriving DecidableEq

abbrev CheckedInput (signature : List Nat) :=
  { input : Input signature // input.Admissible }

def checkInput (input : Input signature) :
    Except Error (CheckedInput signature) :=
  if hvisible : input.AttachmentsVisible then
    if hinjective : input.BinderTargetsInjective then
      if hmatch : input.BinderTargetsMatch then
        if henclose : input.BinderTargetsEnclose then
          .ok ⟨input, {
            attachments_visible := hvisible
            binder_targets_injective := hinjective
            binder_targets_match := hmatch
            binder_targets_enclose := henclose
          }⟩
        else .error .binderDoesNotEncloseSite
      else .error .binderKindOrArityMismatch
    else .error .duplicateBinderTarget
  else .error .attachmentNotVisible

theorem checkInput_sound
    (hcheck : checkInput input = .ok checked) :
    checked.val = input ∧ input.Admissible := by
  unfold checkInput at hcheck
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  cases hcheck
  refine ⟨rfl, ?_⟩
  constructor <;> assumption

theorem checkInput_complete (hadmissible : input.Admissible) :
    checkInput input = .ok ⟨input, hadmissible⟩ := by
  unfold checkInput
  simp only [dif_pos hadmissible.attachments_visible,
    dif_pos hadmissible.binder_targets_injective,
    dif_pos hadmissible.binder_targets_match,
    dif_pos hadmissible.binder_targets_enclose]

theorem checkInput_iff :
    (∃ checked, checkInput input = .ok checked ∧ checked.val = input) ↔
      input.Admissible := by
  constructor
  · rintro ⟨checked, hcheck, rfl⟩
    exact checked.property
  · intro hadmissible
    exact ⟨⟨input, hadmissible⟩, input.checkInput_complete hadmissible, rfl⟩

theorem related_eq_or_both_visible (input : Input signature)
    (hadmissible : input.Admissible)
    {left right : Fin input.frame.val.wireCount}
    (hrelated : input.attachmentPartition.related left right = true) :
    left = right ∨
      (input.frame.val.Encloses (input.frame.val.wires left).scope input.site ∧
        input.frame.val.Encloses (input.frame.val.wires right).scope input.site) := by
  let relation : Fin input.frame.val.wireCount →
      Fin input.frame.val.wireCount → Prop := fun first second =>
    first = second ∨
      (input.frame.val.Encloses (input.frame.val.wires first).scope input.site ∧
        input.frame.val.Encloses (input.frame.val.wires second).scope input.site)
  apply FinitePartition.least
    (relation := relation)
    (fun index => Or.inl rfl)
    (fun h => by
      rcases h with heq | hvisible
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hvisible.2, hvisible.1⟩)
    (fun hfirst hsecond => by
      rcases hfirst with rfl | hfirstVisible
      · exact hsecond
      rcases hsecond with rfl | hsecondVisible
      · exact Or.inr hfirstVisible
      · exact Or.inr ⟨hfirstVisible.1, hsecondVisible.2⟩)
    (fun edge hedge => by
      rw [input.mem_attachmentEdges_iff] at hedge
      rcases hedge with ⟨leftPosition, rightPosition, _, rfl⟩
      exact Or.inr ⟨
        hadmissible.attachments_visible leftPosition,
        hadmissible.attachments_visible rightPosition⟩)
    hrelated

/-- Original host wires represented by one dense quotient wire. -/
def classWires (input : Input signature) (quotient : input.wireQuotient.Carrier) :
    List (Fin input.frame.val.wireCount) :=
  filterFin fun wire => decide (input.quotientWire wire = quotient)

@[simp] theorem mem_classWires (input : Input signature)
    (quotient : input.wireQuotient.Carrier)
    (wire : Fin input.frame.val.wireCount) :
    wire ∈ input.classWires quotient ↔ input.quotientWire wire = quotient := by
  simp [classWires]

theorem classWires_nodup (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    (input.classWires quotient).Nodup :=
  filterFin_nodup _

theorem classWires_nonempty (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    (input.classWires quotient).length > 0 := by
  obtain ⟨wire, hwire⟩ :=
    input.attachmentPartition.classIndex_surjective
      input.attachmentPartition_normalized quotient
  have hmem : wire ∈ input.classWires quotient :=
    (input.mem_classWires quotient wire).2 hwire
  cases hclass : input.classWires quotient with
  | nil => simp [hclass] at hmem
  | cons head tail => simp

def firstClassWire (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    Fin input.frame.val.wireCount :=
  (input.classWires quotient).get ⟨0, input.classWires_nonempty quotient⟩

@[simp] theorem quotientWire_firstClassWire (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    input.quotientWire (input.firstClassWire quotient) = quotient := by
  exact (input.mem_classWires quotient _).1 (List.get_mem _ _)

/-- Pick the outer member of a comparable pair, with stable left tie-break. -/
def chooseOuter (diagram : ConcreteDiagram)
    (left right : Fin diagram.regionCount) : Fin diagram.regionCount :=
  if diagram.Encloses left right then left else right

def outermostFrom (diagram : ConcreteDiagram) :
    Fin diagram.regionCount → List (Fin diagram.regionCount) →
      Fin diagram.regionCount
  | current, [] => current
  | current, next :: tail =>
      outermostFrom diagram (chooseOuter diagram current next) tail

theorem outermostFrom_encloses_of_common
    (diagram : CheckedDiagram signature)
    (site current : Fin diagram.val.regionCount)
    (tail : List (Fin diagram.val.regionCount))
    (hcurrent : diagram.val.Encloses current site)
    (htail : ∀ region, region ∈ tail → diagram.val.Encloses region site) :
    diagram.val.Encloses (outermostFrom diagram.val current tail) current ∧
      ∀ region, region ∈ tail →
        diagram.val.Encloses (outermostFrom diagram.val current tail) region := by
  induction tail generalizing current with
  | nil => exact ⟨ConcreteDiagram.Encloses.refl _ _, by simp⟩
  | cons next tail ih =>
      have hnext : diagram.val.Encloses next site := htail next (by simp)
      have hcomparable := diagram.val.enclosingRegions_comparable
        hcurrent hnext
      have hchosenCurrent :
          diagram.val.Encloses (chooseOuter diagram.val current next) current := by
        rcases hcomparable with hcurrentNext | hnextCurrent
        · simp [chooseOuter, hcurrentNext,
            ConcreteDiagram.Encloses.refl]
        · by_cases hcurrentNext : diagram.val.Encloses current next
          · simp [chooseOuter, hcurrentNext,
              ConcreteDiagram.Encloses.refl]
          · simpa [chooseOuter, hcurrentNext] using hnextCurrent
      have hchosenNext :
          diagram.val.Encloses (chooseOuter diagram.val current next) next := by
        by_cases hcurrentNext : diagram.val.Encloses current next
        · simp [chooseOuter, hcurrentNext]
        · simp [chooseOuter, hcurrentNext,
            ConcreteDiagram.Encloses.refl]
      have hchosenSite :
          diagram.val.Encloses (chooseOuter diagram.val current next) site :=
        ConcreteElaboration.checked_encloses_trans diagram.property
          hchosenCurrent hcurrent
      have htailRest : ∀ region, region ∈ tail →
          diagram.val.Encloses region site := by
        intro region hregion
        exact htail region (by simp [hregion])
      have hresult := ih (chooseOuter diagram.val current next)
        hchosenSite htailRest
      constructor
      · exact ConcreteElaboration.checked_encloses_trans diagram.property
          hresult.1 hchosenCurrent
      · intro region hregion
        rw [List.mem_cons] at hregion
        rcases hregion with rfl | hregion
        · exact ConcreteElaboration.checked_encloses_trans diagram.property
            hresult.1 hchosenNext
        · exact hresult.2 region hregion

def classScopes (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    List (Fin input.frame.val.regionCount) :=
  (input.classWires quotient).map fun wire =>
    (input.frame.val.wires wire).scope

def classAllVisible (input : Input signature)
    (quotient : input.wireQuotient.Carrier) : Prop :=
  ∀ wire, wire ∈ input.classWires quotient →
    input.frame.val.Encloses (input.frame.val.wires wire).scope input.site

instance (input : Input signature) (quotient : input.wireQuotient.Carrier) :
    Decidable (input.classAllVisible quotient) := by
  unfold classAllVisible
  infer_instance

/-- Deterministic outermost class-member scope; singleton nonattachments retain theirs. -/
def coalescedScope (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    Fin input.frame.val.regionCount :=
  let first := input.firstClassWire quotient
  if input.classAllVisible quotient then
    outermostFrom input.frame.val (input.frame.val.wires first).scope
      (input.classWires quotient |>.map fun wire =>
        (input.frame.val.wires wire).scope)
  else
    (input.frame.val.wires first).scope

theorem classWires_related (input : Input signature)
    (quotient : input.wireQuotient.Carrier)
    {left right : Fin input.frame.val.wireCount}
    (hleft : left ∈ input.classWires quotient)
    (hright : right ∈ input.classWires quotient) :
    input.attachmentPartition.related left right = true := by
  rw [← input.quotientWire_eq_iff]
  exact (input.mem_classWires quotient left).1 hleft |>.trans
    ((input.mem_classWires quotient right).1 hright).symm

theorem coalescedScope_encloses_member (input : Input signature)
    (hadmissible : input.Admissible)
    (quotient : input.wireQuotient.Carrier)
    (wire : Fin input.frame.val.wireCount)
    (hmember : wire ∈ input.classWires quotient) :
    input.frame.val.Encloses (input.coalescedScope quotient)
      (input.frame.val.wires wire).scope := by
  by_cases hall : input.classAllVisible quotient
  · simp only [coalescedScope, hall, ↓reduceIte]
    let first := input.firstClassWire quotient
    have hfirstMember : first ∈ input.classWires quotient :=
      (input.mem_classWires quotient first).2
        (input.quotientWire_firstClassWire quotient)
    have hfirstVisible := hall first hfirstMember
    have hscopesVisible : ∀ region,
        region ∈ input.classScopes quotient →
          input.frame.val.Encloses region input.site := by
      intro region hregion
      rw [classScopes, List.mem_map] at hregion
      rcases hregion with ⟨sourceWire, hsource, rfl⟩
      exact hall sourceWire hsource
    have houter := outermostFrom_encloses_of_common input.frame input.site
      (input.frame.val.wires first).scope (input.classScopes quotient)
      hfirstVisible hscopesVisible
    apply houter.2
    rw [classScopes, List.mem_map]
    exact ⟨wire, hmember, rfl⟩
  · have hnotAll : ∃ bad, bad ∈ input.classWires quotient ∧
        ¬ input.frame.val.Encloses
          (input.frame.val.wires bad).scope input.site := by
      exact Classical.byContradiction fun hnone => hall (by
        intro bad hbadMember
        exact Classical.byContradiction fun hbadNotVisible =>
          hnone ⟨bad, hbadMember, hbadNotVisible⟩)
    obtain ⟨bad, hbadMember, hbadNotVisible⟩ := hnotAll
    have member_eq_bad : ∀ candidate,
        candidate ∈ input.classWires quotient → candidate = bad := by
      intro candidate hcandidate
      rcases input.related_eq_or_both_visible hadmissible
          (input.classWires_related quotient hcandidate hbadMember) with
        heq | hvisible
      · exact heq
      · exact False.elim (hbadNotVisible hvisible.2)
    have hwire : wire = input.firstClassWire quotient := by
      rw [member_eq_bad wire hmember,
        member_eq_bad (input.firstClassWire quotient)
          ((input.mem_classWires quotient _).2
            (input.quotientWire_firstClassWire quotient))]
    subst wire
    simpa only [coalescedScope, hall, ↓reduceIte] using
      ConcreteDiagram.Encloses.refl input.frame.val
        (input.frame.val.wires (input.firstClassWire quotient)).scope

/-- Exact endpoint union of an attachment class, in stable old-wire order. -/
def coalescedEndpoints (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    List (CEndpoint input.frame.val.nodeCount) :=
  (input.classWires quotient).flatMap fun wire =>
    (input.frame.val.wires wire).endpoints

def coalesceFrameRaw (input : Input signature) : ConcreteDiagram where
  regionCount := input.frame.val.regionCount
  nodeCount := input.frame.val.nodeCount
  wireCount := input.wireQuotient.count
  root := input.frame.val.root
  regions := input.frame.val.regions
  nodes := input.frame.val.nodes
  wires quotient := {
    scope := input.coalescedScope quotient
    endpoints := input.coalescedEndpoints quotient
  }

@[simp] theorem coalesceFrameRaw_regionCount (input : Input signature) :
    input.coalesceFrameRaw.regionCount = input.frame.val.regionCount := rfl

@[simp] theorem coalesceFrameRaw_nodeCount (input : Input signature) :
    input.coalesceFrameRaw.nodeCount = input.frame.val.nodeCount := rfl

@[simp] theorem coalesceFrameRaw_wireCount (input : Input signature) :
    input.coalesceFrameRaw.wireCount = input.wireQuotient.count := rfl

@[simp] theorem coalesceFrameRaw_regions (input : Input signature)
    (region : Fin input.coalesceFrameRaw.regionCount) :
    input.coalesceFrameRaw.regions region = input.frame.val.regions region := rfl

@[simp] theorem coalesceFrameRaw_nodes (input : Input signature)
    (node : Fin input.coalesceFrameRaw.nodeCount) :
    input.coalesceFrameRaw.nodes node = input.frame.val.nodes node := rfl

@[simp] theorem coalesceFrameRaw_wire (input : Input signature)
    (wire : Fin input.coalesceFrameRaw.wireCount) :
    input.coalesceFrameRaw.wires wire = {
      scope := input.coalescedScope wire
      endpoints := input.coalescedEndpoints wire
    } := rfl

@[simp] theorem mem_coalescedEndpoints (input : Input signature)
    (quotient : input.wireQuotient.Carrier)
    (endpoint : CEndpoint input.frame.val.nodeCount) :
    endpoint ∈ input.coalescedEndpoints quotient ↔
      ∃ wire, wire ∈ input.classWires quotient ∧
        endpoint ∈ (input.frame.val.wires wire).endpoints := by
  simp [coalescedEndpoints]

private theorem endpointLists_nodup
    (frame : CheckedDiagram signature)
    (wires : List (Fin frame.val.wireCount))
    (hnodup : wires.Nodup) :
    (wires.flatMap fun wire => (frame.val.wires wire).endpoints).Nodup := by
  induction wires with
  | nil => simp
  | cons wire tail ih =>
      rw [List.flatMap_cons, List.nodup_append]
      have hparts := List.nodup_cons.mp hnodup
      refine ⟨frame.property.endpoints_are_nodup wire, ih hparts.2, ?_⟩
      intro first hfirst second hsecond heq
      subst second
      rw [List.mem_flatMap] at hsecond
      rcases hsecond with ⟨other, hother, hendpoint⟩
      have hwires : wire ≠ other := by
        intro heq
        subst other
        exact hparts.1 hother
      have hdisjoint := frame.property.wire_endpoints_are_disjoint wire other
        (by simpa using hwires) _ hfirst
      simp [ConcreteDiagram.EndpointOccurs, hendpoint] at hdisjoint

theorem coalescedEndpoints_nodup (input : Input signature)
    (quotient : input.wireQuotient.Carrier) :
    (input.coalescedEndpoints quotient).Nodup :=
  endpointLists_nodup input.frame (input.classWires quotient)
    (input.classWires_nodup quotient)

theorem coalesceFrameRaw_climb (input : Input signature)
    (steps : Nat) (region : Fin input.frame.val.regionCount) :
    input.coalesceFrameRaw.climb steps region =
      input.frame.val.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      cases hparent : (input.frame.val.regions region).parent? with
      | none =>
          simp [ConcreteDiagram.climb, coalesceFrameRaw_regions, hparent]
      | some parent =>
          simp [ConcreteDiagram.climb, coalesceFrameRaw_regions,
            hparent, ih parent]

theorem coalesceFrameRaw_encloses_iff (input : Input signature)
    (ancestor descendant : Fin input.frame.val.regionCount) :
    input.coalesceFrameRaw.Encloses ancestor descendant ↔
      input.frame.val.Encloses ancestor descendant := by
  unfold ConcreteDiagram.Encloses
  constructor <;> rintro ⟨steps, hsteps⟩ <;> refine ⟨steps, ?_⟩
  · rw [input.coalesceFrameRaw_climb] at hsteps
    exact hsteps
  · rw [input.coalesceFrameRaw_climb]
    exact hsteps

theorem endpointOccurs_quotient (input : Input signature)
    (wire : Fin input.frame.val.wireCount)
    (endpoint : CEndpoint input.frame.val.nodeCount)
    (hoccurs : input.frame.val.EndpointOccurs wire endpoint) :
    input.coalesceFrameRaw.EndpointOccurs (input.quotientWire wire) endpoint := by
  change endpoint ∈ input.coalescedEndpoints (input.quotientWire wire)
  rw [input.mem_coalescedEndpoints]
  exact ⟨wire, (input.mem_classWires _ wire).2 rfl, hoccurs⟩

theorem coalesceFrameRaw_wellFormed (input : Input signature)
    (hadmissible : input.Admissible) :
    input.coalesceFrameRaw.WellFormed signature where
  root_is_sheet := input.frame.property.root_is_sheet
  only_root_is_sheet := input.frame.property.only_root_is_sheet
  all_regions_reach_root := by
    intro region
    unfold ConcreteDiagram.ReachesRoot
    rw [input.coalesceFrameRaw_encloses_iff]
    exact input.frame.property.all_regions_reach_root region
  atom_binders_are_bubbles := by
    unfold ConcreteDiagram.AtomBindersAreBubbles
    intro node
    change Fin input.frame.val.nodeCount at node
    have hold := input.frame.property.atom_binders_are_bubbles node
    cases hnode : input.frame.val.nodes node with
    | term => simp [coalesceFrameRaw_nodes, hnode]
    | named => simp [coalesceFrameRaw_nodes, hnode]
    | atom region binder =>
        simp only [hnode] at hold
        simpa [coalesceFrameRaw_nodes, coalesceFrameRaw_regions, hnode] using hold
  atom_binders_enclose := by
    intro node
    change Fin input.frame.val.nodeCount at node
    simp only [coalesceFrameRaw_nodes]
    cases hnode : input.frame.val.nodes node with
    | term => trivial
    | named => trivial
    | atom region binder =>
        simp only
        rw [input.coalesceFrameRaw_encloses_iff]
        simpa only [hnode] using input.frame.property.atom_binders_enclose node
  named_references_resolve := by
    unfold ConcreteDiagram.NamedReferencesResolve
    intro node
    change Fin input.frame.val.nodeCount at node
    have hold := input.frame.property.named_references_resolve node
    cases hnode : input.frame.val.nodes node with
    | term => simp [coalesceFrameRaw_nodes, hnode]
    | atom => simp [coalesceFrameRaw_nodes, hnode]
    | named region definition arity =>
        simp only [hnode] at hold
        simpa [coalesceFrameRaw_nodes, hnode] using hold
  endpoints_are_valid := by
    intro quotient endpoint hendpoint
    change input.wireQuotient.Carrier at quotient
    change CEndpoint input.frame.val.nodeCount at endpoint
    change endpoint ∈ input.coalescedEndpoints quotient at hendpoint
    rw [input.mem_coalescedEndpoints] at hendpoint
    rcases hendpoint with ⟨wire, _, hwire⟩
    have hvalid := input.frame.property.endpoints_are_valid
      wire endpoint hwire
    unfold ConcreteDiagram.RequiresPort at hvalid ⊢
    cases hnode : input.frame.val.nodes endpoint.node with
    | term =>
        simp [coalesceFrameRaw_nodes, hnode] at hvalid ⊢
        exact hvalid
    | named =>
        simp [coalesceFrameRaw_nodes, hnode] at hvalid ⊢
        exact hvalid
    | atom region binder =>
        cases hbinder : input.frame.val.regions binder <;>
          simp [coalesceFrameRaw_nodes, coalesceFrameRaw_regions,
            hnode, hbinder] at hvalid ⊢ <;> exact hvalid
  endpoints_are_nodup := by
    intro quotient
    exact input.coalescedEndpoints_nodup quotient
  wire_endpoints_are_disjoint := by
    intro first second hne endpoint hfirst
    change Fin input.wireQuotient.count at first second
    change CEndpoint input.frame.val.nodeCount at endpoint
    have hneProp : first ≠ second := by
      intro heq
      subst second
      change (!decide (first = first)) = true at hne
      simp at hne
    change (!decide (endpoint ∈ input.coalescedEndpoints second)) = true
    calc
      _ = !false := congrArg (fun value : Bool => !value)
        (decide_eq_false_iff_not.mpr (by
          intro hsecond
          change endpoint ∈ input.coalescedEndpoints first at hfirst
          rw [input.mem_coalescedEndpoints] at hfirst hsecond
          rcases hfirst with ⟨firstWire, hfirstClass, hfirstEndpoint⟩
          rcases hsecond with ⟨secondWire, hsecondClass, hsecondEndpoint⟩
          by_cases hwires : firstWire = secondWire
          · subst secondWire
            exact hneProp
              (((input.mem_classWires first firstWire).1 hfirstClass).symm.trans
                ((input.mem_classWires second firstWire).1 hsecondClass))
          · have hdisjoint :=
              input.frame.property.wire_endpoints_are_disjoint
                firstWire secondWire (by simpa using hwires) endpoint
                hfirstEndpoint
            simp [ConcreteDiagram.EndpointOccurs, hsecondEndpoint] at hdisjoint))
      _ = true := rfl
  required_ports_are_covered := by
    unfold ConcreteDiagram.RequiredPortsAreCovered
    intro node
    have hcovered := input.frame.property.required_ports_are_covered node
    simp only [coalesceFrameRaw_nodes, coalesceFrameRaw_regions]
    cases hnode : input.frame.val.nodes node with
    | term region freePorts term =>
        simp only [hnode] at hcovered ⊢
        rcases hcovered.1 with ⟨wire, houtput⟩
        refine ⟨⟨input.quotientWire wire,
          input.endpointOccurs_quotient wire _ houtput⟩, ?_⟩
        intro index
        obtain ⟨wire, hport⟩ := hcovered.2 index
        exact ⟨input.quotientWire wire,
          input.endpointOccurs_quotient wire _ hport⟩
    | atom region binder =>
        simp only [hnode] at hcovered ⊢
        cases hbinder : input.frame.val.regions binder with
        | sheet => trivial
        | cut parent => trivial
        | bubble parent arity =>
            simp only [hbinder] at hcovered ⊢
            intro index
            obtain ⟨wire, hport⟩ := hcovered index
            exact ⟨input.quotientWire wire,
              input.endpointOccurs_quotient wire _ hport⟩
    | named region definition arity =>
        simp only [hnode] at hcovered ⊢
        intro index
        obtain ⟨wire, hport⟩ := hcovered index
        exact ⟨input.quotientWire wire,
          input.endpointOccurs_quotient wire _ hport⟩
  wire_scopes_enclose := by
    intro quotient endpoint hendpoint
    change input.wireQuotient.Carrier at quotient
    change CEndpoint input.frame.val.nodeCount at endpoint
    change endpoint ∈ input.coalescedEndpoints quotient at hendpoint
    rw [input.mem_coalescedEndpoints] at hendpoint
    rcases hendpoint with ⟨wire, hclass, hwire⟩
    have hscope := input.coalescedScope_encloses_member
      hadmissible quotient wire hclass
    have hold := input.frame.property.wire_scopes_enclose wire endpoint hwire
    rw [input.coalesceFrameRaw_encloses_iff]
    exact ConcreteElaboration.checked_encloses_trans input.frame.property hscope hold

def coalesceFrame (input : Input signature) (hadmissible : input.Admissible) :
    CheckedDiagram signature :=
  ⟨input.coalesceFrameRaw, input.coalesceFrameRaw_wellFormed hadmissible⟩

/-- Stable material/proxy and internal-wire blocks for plugging. -/
structure PlugLayout (input : Input signature) where
  materialRegions : SurvivorDomain input.pattern.val.diagram.regionCount := {
    survives region := decide (input.binderSpine.IsMaterialRegion region)
  }
  internalWires : SurvivorDomain input.pattern.val.diagram.wireCount := {
    survives wire := decide (wire ∉ input.pattern.val.exposedWires)
  }

namespace PlugLayout

def regionCount (layout : PlugLayout input) : Nat :=
  input.frame.val.regionCount + layout.materialRegions.count

def nodeCount (_layout : PlugLayout input) : Nat :=
  input.frame.val.nodeCount + input.pattern.val.diagram.nodeCount

def wireCount (layout : PlugLayout input) : Nat :=
  input.wireQuotient.count + layout.internalWires.count

def frameRegion (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) : Fin layout.regionCount :=
  Fin.castAdd layout.materialRegions.count region

def materialRegion (layout : PlugLayout input)
    (region : layout.materialRegions.Carrier) : Fin layout.regionCount :=
  Fin.natAdd input.frame.val.regionCount region

def frameNode (layout : PlugLayout input)
    (node : Fin input.frame.val.nodeCount) : Fin layout.nodeCount :=
  Fin.castAdd input.pattern.val.diagram.nodeCount node

def patternNode (layout : PlugLayout input)
    (node : Fin input.pattern.val.diagram.nodeCount) : Fin layout.nodeCount :=
  Fin.natAdd input.frame.val.nodeCount node

def frameWire (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) : Fin layout.wireCount :=
  Fin.castAdd layout.internalWires.count wire

def internalWire (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) : Fin layout.wireCount :=
  Fin.natAdd input.wireQuotient.count wire

def bodyRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.materialRegions.index? region with
  | some material => layout.materialRegion material
  | none => layout.frameRegion input.site

def proxies (_layout : PlugLayout input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  (allFin input.binderSpine.proxyCount).map input.binderSpine.proxy

theorem proxies_nodup (layout : PlugLayout input) : layout.proxies.Nodup :=
  List.Pairwise.map (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right) input.binderSpine.proxy (by
      intro left right hne heq
      exact hne (input.binderSpine.proxy_injective heq))
    (allFin_nodup _)

def proxyIndex? (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Option (Fin input.binderSpine.proxyCount) :=
  (indexOf? layout.proxies region).map (Fin.cast (by
    simp [proxies, allFin_eq_finRange]))

def binderRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.proxyIndex? region with
  | some proxy => layout.frameRegion (input.binderTarget proxy)
  | none => layout.bodyRegion region

def mapPatternRegion (layout : PlugLayout input)
    (region : CRegion input.pattern.val.diagram.regionCount) :
    CRegion layout.regionCount :=
  match region with
  | .sheet => .cut (layout.frameRegion input.site)
  | .cut parent => .cut (layout.bodyRegion parent)
  | .bubble parent arity => .bubble (layout.bodyRegion parent) arity

def mapPatternNode (layout : PlugLayout input)
    (node : CNode input.pattern.val.diagram.regionCount) :
    CNode layout.regionCount :=
  match node with
  | .term region freePorts term =>
      .term (layout.bodyRegion region) freePorts term
  | .atom region binder =>
      .atom (layout.bodyRegion region) (layout.binderRegion binder)
  | .named region definition arity =>
      .named (layout.bodyRegion region) definition arity

def mapPatternEndpoint (layout : PlugLayout input)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount) :
    CEndpoint layout.nodeCount :=
  { node := layout.patternNode endpoint.node, port := endpoint.port }

def mapPatternWire (layout : PlugLayout input)
    (wire : CWire input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount) :
    CWire layout.regionCount layout.nodeCount :=
  { scope := layout.bodyRegion wire.scope
    endpoints := wire.endpoints.map layout.mapPatternEndpoint }

/-- First ordered boundary position carrying one exposed wire identity. -/
def exposedPosition (_layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    Fin input.pattern.val.boundary.length :=
  (indexOf? input.pattern.val.boundary
    (input.pattern.val.exposedWires.get external)).get (by
      rw [indexOf?_isSome_iff]
      exact (OpenConcreteDiagram.mem_exposedWires _ _).1
        (List.get_mem _ _))

def exposedAttachment (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.wireQuotient.Carrier :=
  input.quotientWire (input.attachment (layout.exposedPosition external))

def boundaryEndpoints (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    List (CEndpoint layout.nodeCount) :=
  (allFin input.pattern.val.exposedWires.length).flatMap fun external =>
    if layout.exposedAttachment external = quotient then
      (input.pattern.val.diagram.wires
        (input.pattern.val.exposedWires.get external)).endpoints.map
          layout.mapPatternEndpoint
    else
      []

def plugRegion (layout : PlugLayout input)
    (region : Fin layout.regionCount) : CRegion layout.regionCount :=
  Fin.addCases
    (fun frameRegion =>
      match input.frame.val.regions frameRegion with
      | .sheet => .sheet
      | .cut parent => .cut (layout.frameRegion parent)
      | .bubble parent arity => .bubble (layout.frameRegion parent) arity)
    (fun material => layout.mapPatternRegion
      (input.pattern.val.diagram.regions
        (layout.materialRegions.origin material))) region

def plugNode (layout : PlugLayout input)
    (node : Fin layout.nodeCount) : CNode layout.regionCount :=
  Fin.addCases
    (fun frameNode =>
      match input.frame.val.nodes frameNode with
      | .term region freePorts term =>
          .term (layout.frameRegion region) freePorts term
      | .atom region binder =>
          .atom (layout.frameRegion region) (layout.frameRegion binder)
      | .named region definition arity =>
          .named (layout.frameRegion region) definition arity)
    (fun patternNode => layout.mapPatternNode
      (input.pattern.val.diagram.nodes patternNode)) node

def plugWire (layout : PlugLayout input)
    (wire : Fin layout.wireCount) : CWire layout.regionCount layout.nodeCount :=
  Fin.addCases
    (fun quotient => {
      scope := layout.frameRegion (input.coalescedScope quotient)
      endpoints :=
        (input.coalescedEndpoints quotient).map (fun endpoint =>
          ({ node := layout.frameNode endpoint.node, port := endpoint.port } :
            CEndpoint layout.nodeCount)) ++ layout.boundaryEndpoints quotient
    })
    (fun internal => layout.mapPatternWire
      (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal))) wire

def plugRaw (layout : PlugLayout input) : ConcreteDiagram where
  regionCount := layout.regionCount
  nodeCount := layout.nodeCount
  wireCount := layout.wireCount
  root := layout.frameRegion input.frame.val.root
  regions := layout.plugRegion
  nodes := layout.plugNode
  wires := layout.plugWire

end PlugLayout

def plugLayout (input : Input signature) : PlugLayout input := {}

def spliceChecked (signature : List Nat) (input : Input signature) :
    Except Error (CheckedDiagram signature) :=
  match checkInput input with
  | .error error => .error error
  | .ok _ =>
      match checkWellFormed signature input.plugLayout.plugRaw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok result

theorem spliceChecked_sound
    (hsplice : spliceChecked signature input = .ok result) :
    result.val = input.plugLayout.plugRaw ∧
      input.Admissible ∧ result.val.WellFormed signature := by
  unfold spliceChecked at hsplice
  split at hsplice
  · contradiction
  · rename_i checkedInput hinput
    split at hsplice
    · contradiction
    · rename_i checkedResult hresult
      cases hsplice
      exact ⟨checkWellFormed_preserves_input hresult,
        (checkInput_sound hinput).2, result.property⟩

end Input

end Splice

end VisualProof.Diagram
