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

private theorem splice_climb_prefix_exists {d : ConcreteDiagram}
    {start finish : Fin d.regionCount} {first second : Nat}
    (hle : first ≤ second)
    (hfinish : d.climb second start = some finish) :
    ∃ middle, d.climb first start = some middle := by
  induction first generalizing start second with
  | zero => exact ⟨start, rfl⟩
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases hparent : (d.regions start).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hfinish
          | some parent =>
              have htail : d.climb second parent = some finish := by
                simpa [ConcreteDiagram.climb, hparent] using hfinish
              obtain ⟨middle, hmiddle⟩ :=
                ih (Nat.le_of_succ_le_succ hle) htail
              exact ⟨middle, by
                simpa [ConcreteDiagram.climb, hparent] using hmiddle⟩

private theorem splice_climb_cancel_prefix {d : ConcreteDiagram}
    {start middle finish : Fin d.regionCount} {first second : Nat}
    (hle : first ≤ second)
    (hfirst : d.climb first start = some middle)
    (hsecond : d.climb second start = some finish) :
    d.climb (second - first) middle = some finish := by
  induction first generalizing start second with
  | zero =>
      have heq : start = middle := Option.some.inj hfirst
      subst middle
      simpa using hsecond
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases hparent : (d.regions start).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hfirst
          | some parent =>
              have hfirstTail : d.climb first parent = some middle := by
                simpa [ConcreteDiagram.climb, hparent] using hfirst
              have hsecondTail : d.climb second parent = some finish := by
                simpa [ConcreteDiagram.climb, hparent] using hsecond
              simpa using ih (Nat.le_of_succ_le_succ hle)
                hfirstTail hsecondTail

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
  materialRegions_exact : ∀ region,
      materialRegions.survives region =
        decide (input.binderSpine.IsMaterialRegion region) := by
    intro region
    rfl
  internalWires : SurvivorDomain input.pattern.val.diagram.wireCount := {
    survives wire := decide (wire ∉ input.pattern.val.exposedWires)
  }
  internalWires_exact : ∀ wire,
      internalWires.survives wire =
        decide (wire ∉ input.pattern.val.exposedWires) := by
    intro wire
    rfl

namespace PlugLayout

@[simp] theorem materialRegions_survives_iff (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    layout.materialRegions.survives region = true ↔
      input.binderSpine.IsMaterialRegion region := by
  rw [layout.materialRegions_exact]
  exact decide_eq_true_iff

@[simp] theorem internalWires_survives_iff (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.internalWires.survives wire = true ↔
      wire ∉ input.pattern.val.exposedWires := by
  rw [layout.internalWires_exact]
  exact decide_eq_true_iff

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

def quotientBlockWire (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) : Fin layout.wireCount :=
  Fin.castAdd layout.internalWires.count wire

def internalBlockWire (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) : Fin layout.wireCount :=
  Fin.natAdd input.wireQuotient.count wire

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

theorem frameRegion_injective (layout : PlugLayout input) :
    Function.Injective layout.frameRegion := by
  intro left right heq
  apply Fin.ext
  exact congrArg (fun index => index.val) heq

theorem materialRegion_injective (layout : PlugLayout input) :
    Function.Injective layout.materialRegion := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg Fin.val heq
  simp [materialRegion] at hvals
  omega

theorem frameRegion_ne_materialRegion (layout : PlugLayout input)
    (frame : Fin input.frame.val.regionCount)
    (material : layout.materialRegions.Carrier) :
    layout.frameRegion frame ≠ layout.materialRegion material := by
  intro heq
  have hvals := congrArg Fin.val heq
  simp [frameRegion, materialRegion] at hvals
  omega

def materialIndex (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.materialRegions.Carrier :=
  layout.materialRegions.index region
    ((layout.materialRegions_survives_iff region).2 hmaterial)

@[simp] theorem bodyRegion_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.bodyRegion region = layout.materialRegion
      (layout.materialIndex region hmaterial) := by
  unfold bodyRegion materialIndex
  rw [layout.materialRegions.index?_index]

@[simp] theorem bodyRegion_origin (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.bodyRegion (layout.materialRegions.origin material) =
      layout.materialRegion material := by
  have hmaterial : input.binderSpine.IsMaterialRegion
      (layout.materialRegions.origin material) :=
    (layout.materialRegions_survives_iff _).1
      (layout.materialRegions.origin_survives material)
  rw [layout.bodyRegion_material _ hmaterial]
  apply congrArg layout.materialRegion
  apply layout.materialRegions.origin_injective
  simp only [materialIndex, layout.materialRegions.origin_index]

theorem bodyRegion_nonmaterial (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : ¬ input.binderSpine.IsMaterialRegion region) :
    layout.bodyRegion region = layout.frameRegion input.site := by
  unfold bodyRegion
  have hfalse : layout.materialRegions.survives region = false := by
    rw [layout.materialRegions_exact]
    simp [hmaterial]
  rw [(layout.materialRegions.index?_eq_none_iff region).2 hfalse]

@[simp] theorem bodyRegion_root (layout : PlugLayout input) :
    layout.bodyRegion input.pattern.val.diagram.root =
      layout.frameRegion input.site := by
  apply layout.bodyRegion_nonmaterial
  simp [BinderSpine.IsMaterialRegion]

@[simp] theorem bodyRegion_proxy (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.bodyRegion (input.binderSpine.proxy index) =
      layout.frameRegion input.site := by
  apply layout.bodyRegion_nonmaterial
  intro hmaterial
  exact hmaterial.2 index rfl

@[simp] theorem bodyRegion_bodyContainer (layout : PlugLayout input) :
    layout.bodyRegion input.binderSpine.bodyContainer =
      layout.frameRegion input.site := by
  by_cases hzero : input.binderSpine.proxyCount = 0
  · rw [input.binderSpine.body_eq_root_of_empty hzero,
      layout.bodyRegion_root]
  · rw [input.binderSpine.body_eq_terminal_of_nonempty hzero,
      layout.bodyRegion_proxy]

theorem frameNode_injective (layout : PlugLayout input) :
    Function.Injective layout.frameNode := by
  intro left right heq
  apply Fin.ext
  exact congrArg (fun index => index.val) heq

theorem patternNode_injective (layout : PlugLayout input) :
    Function.Injective layout.patternNode := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg Fin.val heq
  simp [patternNode] at hvals
  omega

theorem frameNode_ne_patternNode (layout : PlugLayout input)
    (frame : Fin input.frame.val.nodeCount)
    (pattern : Fin input.pattern.val.diagram.nodeCount) :
    layout.frameNode frame ≠ layout.patternNode pattern := by
  intro heq
  have hvals := congrArg Fin.val heq
  simp [frameNode, patternNode] at hvals
  omega

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

def proxyPosition (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) : Fin layout.proxies.length :=
  Fin.cast (by simp [proxies, allFin_eq_finRange]) index

@[simp] theorem proxies_get_proxyPosition (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.proxies.get (layout.proxyPosition index) =
      input.binderSpine.proxy index := by
  simp [proxies, proxyPosition, allFin_eq_finRange]

@[simp] theorem proxyIndex?_proxy (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.proxyIndex? (input.binderSpine.proxy index) = some index := by
  unfold proxyIndex?
  have hlookup : indexOf? layout.proxies
      (input.binderSpine.proxy index) = some (layout.proxyPosition index) := by
    rw [← layout.proxies_get_proxyPosition index]
    exact indexOf?_get_eq_some_of_nodup layout.proxies_nodup _
  rw [hlookup]
  apply congrArg some
  apply Fin.ext
  rfl

theorem proxyIndex?_eq_none_of_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.proxyIndex? region = none := by
  unfold proxyIndex?
  cases hlookup : indexOf? layout.proxies region with
  | none => rfl
  | some found =>
      have hsound := indexOf?_sound hlookup
      have hmember : region ∈ layout.proxies := by
        rw [← hsound]
        exact List.get_mem _ _
      rw [proxies, List.mem_map] at hmember
      rcases hmember with ⟨index, _, hproxy⟩
      exact False.elim (hmaterial.2 index hproxy.symm)

def binderRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.regionCount :=
  match layout.proxyIndex? region with
  | some proxy => layout.frameRegion (input.binderTarget proxy)
  | none => layout.bodyRegion region

@[simp] theorem binderRegion_proxy (layout : PlugLayout input)
    (index : Fin input.binderSpine.proxyCount) :
    layout.binderRegion (input.binderSpine.proxy index) =
      layout.frameRegion (input.binderTarget index) := by
  simp [binderRegion]

@[simp] theorem binderRegion_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    layout.binderRegion region = layout.bodyRegion region := by
  unfold binderRegion
  rw [layout.proxyIndex?_eq_none_of_material region hmaterial]

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

def mapFrameEndpoint (layout : PlugLayout input)
    (endpoint : CEndpoint input.frame.val.nodeCount) :
    CEndpoint layout.nodeCount :=
  { node := layout.frameNode endpoint.node, port := endpoint.port }

theorem mapFrameEndpoint_injective (layout : PlugLayout input) :
    Function.Injective layout.mapFrameEndpoint := by
  intro left right heq
  cases left with
  | mk leftNode leftPort =>
    cases right with
    | mk rightNode rightPort =>
      simp only [mapFrameEndpoint] at heq
      have hnodes : leftNode = rightNode :=
        layout.frameNode_injective (congrArg CEndpoint.node heq)
      have hports : leftPort = rightPort := congrArg CEndpoint.port heq
      subst rightNode
      subst rightPort
      rfl

theorem mapFrameEndpoint_ne_mapPatternEndpoint (layout : PlugLayout input)
    (frame : CEndpoint input.frame.val.nodeCount)
    (pattern : CEndpoint input.pattern.val.diagram.nodeCount) :
    layout.mapFrameEndpoint frame ≠ layout.mapPatternEndpoint pattern := by
  intro heq
  exact layout.frameNode_ne_patternNode frame.node pattern.node
    (congrArg CEndpoint.node heq)

theorem mapPatternEndpoint_injective (layout : PlugLayout input) :
    Function.Injective layout.mapPatternEndpoint := by
  intro left right heq
  cases left with
  | mk leftNode leftPort =>
    cases right with
    | mk rightNode rightPort =>
      simp only [mapPatternEndpoint] at heq
      have hnodes : leftNode = rightNode :=
        layout.patternNode_injective (congrArg CEndpoint.node heq)
      have hports : leftPort = rightPort := congrArg CEndpoint.port heq
      subst rightNode
      subst rightPort
      rfl

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

def boundaryWires (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    List (Fin input.pattern.val.diagram.wireCount) :=
  ((allFin input.pattern.val.exposedWires.length).filter fun external =>
    decide (layout.exposedAttachment external = quotient)).map fun external =>
      input.pattern.val.exposedWires.get external

def boundaryEndpoints (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    List (CEndpoint layout.nodeCount) :=
  ((layout.boundaryWires quotient).flatMap fun wire =>
    (input.pattern.val.diagram.wires wire).endpoints).map
      layout.mapPatternEndpoint

theorem boundaryWires_nodup (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    (layout.boundaryWires quotient).Nodup := by
  unfold boundaryWires
  apply List.Pairwise.map
    (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right)
  · intro left right hne heq
    apply hne
    apply Fin.ext
    exact (List.getElem_inj input.pattern.val.exposedWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using heq)
  · exact List.Pairwise.filter _ (allFin_nodup _)

theorem boundaryEndpoints_nodup (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    (layout.boundaryEndpoints quotient).Nodup := by
  unfold boundaryEndpoints
  apply List.Pairwise.map
    (R := fun left right => left ≠ right)
    (S := fun left right => left ≠ right)
    layout.mapPatternEndpoint
    (fun left right hne heq => hne
      (layout.mapPatternEndpoint_injective heq))
  exact endpointLists_nodup
      ⟨input.pattern.val.diagram,
        input.pattern.property.diagram_well_formed⟩
      (layout.boundaryWires quotient) (layout.boundaryWires_nodup quotient)

theorem mem_boundaryEndpoints (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier)
    (endpoint : CEndpoint layout.nodeCount) :
    endpoint ∈ layout.boundaryEndpoints quotient ↔
      ∃ external : Fin input.pattern.val.exposedWires.length,
        layout.exposedAttachment external = quotient ∧
          ∃ original : CEndpoint input.pattern.val.diagram.nodeCount,
            original ∈ (input.pattern.val.diagram.wires
                (input.pattern.val.exposedWires.get external)).endpoints ∧
              layout.mapPatternEndpoint original = endpoint := by
  simp only [boundaryEndpoints]
  rw [List.mem_map]
  constructor
  · rintro ⟨original, horiginal, heq⟩
    rw [List.mem_flatMap] at horiginal
    obtain ⟨wire, hwire, hendpoint⟩ := horiginal
    rw [boundaryWires, List.mem_map] at hwire
    obtain ⟨external, hexternal, hget⟩ := hwire
    rw [List.mem_filter] at hexternal
    exact ⟨external, (decide_eq_true_iff.mp hexternal.2), original,
      by simpa only [hget] using hendpoint, heq⟩
  · rintro ⟨external, heq, original, horiginal, rfl⟩
    refine ⟨original, ?_, rfl⟩
    rw [List.mem_flatMap]
    refine ⟨input.pattern.val.exposedWires.get external, ?_, horiginal⟩
    rw [boundaryWires, List.mem_map]
    refine ⟨external, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨mem_allFin external, decide_eq_true_iff.mpr heq⟩

def mapFrameRegion (layout : PlugLayout input) :
    CRegion input.frame.val.regionCount → CRegion layout.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (layout.frameRegion parent)
  | .bubble parent arity => .bubble (layout.frameRegion parent) arity

def mapFrameNode (layout : PlugLayout input) :
    CNode input.frame.val.regionCount → CNode layout.regionCount
  | .term region freePorts term =>
      .term (layout.frameRegion region) freePorts term
  | .atom region binder =>
      .atom (layout.frameRegion region) (layout.frameRegion binder)
  | .named region definition arity =>
      .named (layout.frameRegion region) definition arity

@[simp] theorem mapFrameNode_region (layout : PlugLayout input)
    (node : CNode input.frame.val.regionCount) :
    (layout.mapFrameNode node).region = layout.frameRegion node.region := by
  cases node <;> rfl

@[simp] theorem mapPatternNode_region (layout : PlugLayout input)
    (node : CNode input.pattern.val.diagram.regionCount) :
    (layout.mapPatternNode node).region = layout.bodyRegion node.region := by
  cases node <;> rfl

def plugRegion (layout : PlugLayout input)
    (region : Fin layout.regionCount) : CRegion layout.regionCount :=
  Fin.addCases
    (fun frameRegion => layout.mapFrameRegion
      (input.frame.val.regions frameRegion))
    (fun material => layout.mapPatternRegion
      (input.pattern.val.diagram.regions
        (layout.materialRegions.origin material))) region

def plugNode (layout : PlugLayout input)
    (node : Fin layout.nodeCount) : CNode layout.regionCount :=
  Fin.addCases
    (fun frameNode => layout.mapFrameNode (input.frame.val.nodes frameNode))
    (fun patternNode => layout.mapPatternNode
      (input.pattern.val.diagram.nodes patternNode)) node

def plugWire (layout : PlugLayout input)
    (wire : Fin layout.wireCount) : CWire layout.regionCount layout.nodeCount :=
  Fin.addCases
    (fun quotient => {
      scope := layout.frameRegion (input.coalescedScope quotient)
      endpoints :=
        (input.coalescedEndpoints quotient).map layout.mapFrameEndpoint ++
          layout.boundaryEndpoints quotient
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

@[simp] theorem plugWire_quotientBlockWire (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) :
    layout.plugWire (layout.quotientBlockWire wire) = {
      scope := layout.frameRegion (input.coalescedScope wire)
      endpoints :=
        (input.coalescedEndpoints wire).map layout.mapFrameEndpoint ++
          layout.boundaryEndpoints wire
    } := by
  simp [plugWire, quotientBlockWire]

@[simp] theorem plugWire_internalBlockWire (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (wire : layout.internalWires.Carrier) :
    layout.plugWire (layout.internalBlockWire wire) =
      layout.mapPatternWire (input.pattern.val.diagram.wires
        (layout.internalWires.origin wire)) := by
  simp [plugWire, internalBlockWire]

@[simp] theorem plugRegion_frameRegion (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    layout.plugRegion (layout.frameRegion region) =
      layout.mapFrameRegion (input.frame.val.regions region) := by
  simp [plugRegion, frameRegion]

@[simp] theorem plugRegion_materialRegion (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    layout.plugRegion (layout.materialRegion material) =
      layout.mapPatternRegion (input.pattern.val.diagram.regions
        (layout.materialRegions.origin material)) := by
  simp [plugRegion, materialRegion]

@[simp] theorem plugNode_frameNode (layout : PlugLayout input)
    (node : Fin input.frame.val.nodeCount) :
    layout.plugNode (layout.frameNode node) =
      layout.mapFrameNode (input.frame.val.nodes node) := by
  simp [plugNode, frameNode]

@[simp] theorem plugNode_patternNode (layout : PlugLayout input)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    layout.plugNode (layout.patternNode node) =
      layout.mapPatternNode (input.pattern.val.diagram.nodes node) := by
  simp [plugNode, patternNode]

theorem bodyRegion_parent_exact (layout : PlugLayout input)
    (region parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hparent : (input.pattern.val.diagram.regions region).parent? = some parent) :
    (layout.plugRaw.regions (layout.bodyRegion region)).parent? =
      some (layout.bodyRegion parent) := by
  rw [layout.bodyRegion_material region hmaterial]
  change (layout.plugRegion (layout.materialRegion
    (layout.materialIndex region hmaterial))).parent? = _
  rw [layout.plugRegion_materialRegion]
  have horigin : layout.materialRegions.origin
      (layout.materialIndex region hmaterial) = region := by
    exact layout.materialRegions.origin_index region
      ((layout.materialRegions_survives_iff region).2 hmaterial)
  rw [horigin]
  cases hregion : input.pattern.val.diagram.regions region with
  | sheet =>
      rw [hregion] at hparent
      contradiction
  | cut actualParent =>
      simp only [hregion, CRegion.parent?] at hparent
      cases hparent
      rfl
  | bubble actualParent arity =>
      simp only [hregion, CRegion.parent?] at hparent
      cases hparent
      rfl

theorem bodyRegion_parent_encloses (layout : PlugLayout input)
    (region parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hparent : (input.pattern.val.diagram.regions region).parent? = some parent) :
    layout.plugRaw.Encloses (layout.bodyRegion parent)
      (layout.bodyRegion region) := by
  refine ⟨⟨1, by
    simp only [plugRaw, regionCount]
    have := input.frame.val.root.isLt
    omega⟩, ?_⟩
  simp only [ConcreteDiagram.climb,
    layout.bodyRegion_parent_exact region parent hmaterial hparent]

theorem nonmaterial_parent_eq_bodyContainer (input : Input signature)
    (region parent : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hparent : (input.pattern.val.diagram.regions region).parent? = some parent)
    (hparentNonmaterial : ¬ input.binderSpine.IsMaterialRegion parent) :
    parent = input.binderSpine.bodyContainer := by
  by_cases hroot : parent = input.pattern.val.diagram.root
  · by_cases hzero : input.binderSpine.proxyCount = 0
    · exact hroot.trans
        (input.binderSpine.body_eq_root_of_empty hzero).symm
    · have hfirst := input.terminalBody.root_direct_child hzero region (by
        simpa only [hroot] using hparent)
      exact False.elim (hmaterial.2 ⟨0, Nat.pos_of_ne_zero hzero⟩ hfirst)
  · have hproxy : ∃ index : Fin input.binderSpine.proxyCount,
        parent = input.binderSpine.proxy index := by
      exact Classical.byContradiction fun hnone => hparentNonmaterial ⟨hroot, by
        intro index heq
        exact hnone ⟨index, heq⟩⟩
    obtain ⟨index, hindex⟩ := hproxy
    by_cases hnonterminal : index.val + 1 < input.binderSpine.proxyCount
    · have hnext := input.terminalBody.nonterminal_direct_child
        index hnonterminal region (by simpa only [hindex] using hparent)
      exact False.elim (hmaterial.2 ⟨index.val + 1, hnonterminal⟩ hnext)
    · have hcount : index.val + 1 = input.binderSpine.proxyCount := by
        have := index.isLt
        omega
      have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
        have := index.isLt
        omega
      let terminal : Fin input.binderSpine.proxyCount :=
        ⟨input.binderSpine.proxyCount - 1, by omega⟩
      have hterminal : index = terminal := by
        apply Fin.ext
        simp only [terminal]
        omega
      rw [hindex, hterminal]
      exact (input.binderSpine.body_eq_terminal_of_nonempty hnonzero).symm

theorem material_climb_body_and_plug_site (layout : PlugLayout input) :
    ∀ (fuel : Nat) (region : Fin input.pattern.val.diagram.regionCount),
      input.binderSpine.IsMaterialRegion region →
      input.pattern.val.diagram.climb fuel region =
        some input.pattern.val.diagram.root →
      ∃ steps : Nat,
        input.pattern.val.diagram.climb steps region =
            some input.binderSpine.bodyContainer ∧
          layout.plugRaw.climb steps (layout.bodyRegion region) =
            some (layout.frameRegion input.site) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region hmaterial hclimb
      have hroot : region = input.pattern.val.diagram.root :=
        Option.some.inj hclimb
      exact False.elim (hmaterial.1 hroot)
  | succ fuel ih =>
      intro region hmaterial hclimb
      cases hparent : (input.pattern.val.diagram.regions region).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hclimb
      | some parent =>
          have htail : input.pattern.val.diagram.climb fuel parent =
              some input.pattern.val.diagram.root := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          by_cases hparentMaterial :
              input.binderSpine.IsMaterialRegion parent
          · obtain ⟨steps, horiginal, hplug⟩ :=
              ih parent hparentMaterial htail
            refine ⟨1 + steps, ?_, ?_⟩
            · exact ConcreteElaboration.climb_add (by
                simp [ConcreteDiagram.climb, hparent]) horiginal
            · have hstep : layout.plugRaw.climb 1
                  (layout.bodyRegion region) =
                  some (layout.bodyRegion parent) := by
                simp only [ConcreteDiagram.climb]
                rw [layout.bodyRegion_parent_exact
                  region parent hmaterial hparent]
                rfl
              exact ConcreteElaboration.climb_add hstep hplug
          · have hbody := nonmaterial_parent_eq_bodyContainer (input := input)
              region parent hmaterial hparent hparentMaterial
            refine ⟨1, ?_, ?_⟩
            · simpa [ConcreteDiagram.climb, hparent] using congrArg some hbody
            · simp only [ConcreteDiagram.climb]
              rw [layout.bodyRegion_parent_exact
                region parent hmaterial hparent]
              exact congrArg some
                (layout.bodyRegion_nonmaterial parent hparentMaterial)

theorem material_of_climb_lt_bodyContainer (input : Input signature) :
    ∀ (steps : Nat)
      (region current : Fin input.pattern.val.diagram.regionCount)
      (position : Nat),
      input.binderSpine.IsMaterialRegion region →
      input.pattern.val.diagram.climb steps region =
        some input.binderSpine.bodyContainer →
      position < steps →
      input.pattern.val.diagram.climb position region = some current →
      input.binderSpine.IsMaterialRegion current := by
  intro steps
  induction steps with
  | zero =>
      intro region current position _ _ hlt _
      omega
  | succ steps ih =>
      intro region current position hmaterial hbody hlt hposition
      cases position with
      | zero =>
          have heq : region = current := Option.some.inj hposition
          simpa only [← heq] using hmaterial
      | succ position =>
          cases hparent : (input.pattern.val.diagram.regions region).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hbody
          | some parent =>
              have htail : input.pattern.val.diagram.climb steps parent =
                  some input.binderSpine.bodyContainer := by
                simpa [ConcreteDiagram.climb, hparent] using hbody
              have hpositionTail :
                  input.pattern.val.diagram.climb position parent =
                    some current := by
                simpa [ConcreteDiagram.climb, hparent] using hposition
              have hparentMaterial :
                  input.binderSpine.IsMaterialRegion parent := by
                by_cases hcandidate :
                    input.binderSpine.IsMaterialRegion parent
                · exact hcandidate
                · have hparentBody := nonmaterial_parent_eq_bodyContainer
                    (input := input) region parent hmaterial hparent hcandidate
                  obtain ⟨rootSteps, hbodyRoot⟩ :=
                    input.pattern.property.diagram_well_formed
                      |>.all_regions_reach_root input.binderSpine.bodyContainer
                  have hcycleRoot := ConcreteElaboration.climb_add
                    htail hbodyRoot
                  rw [hparentBody] at hcycleRoot
                  have hunique :=
                    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique
                      input.pattern.val.diagram
                      input.pattern.property.diagram_well_formed.root_is_sheet
                      hcycleRoot hbodyRoot
                  omega
              exact ih parent current position hparentMaterial htail
                (by omega) hpositionTail

theorem material_climb_steps_le_count (layout : PlugLayout input)
    {steps : Nat} {region : Fin input.pattern.val.diagram.regionCount}
    (hmaterial : input.binderSpine.IsMaterialRegion region)
    (hclimb : input.pattern.val.diagram.climb steps region =
      some input.binderSpine.bodyContainer) :
    steps ≤ layout.materialRegions.count := by
  let pathIsSome (position : Fin steps) :
      (input.pattern.val.diagram.climb position.val region).isSome = true :=
    Option.isSome_iff_exists.mpr
      (splice_climb_prefix_exists (Nat.le_of_lt position.isLt) hclimb)
  let path (position : Fin steps) :
      Fin input.pattern.val.diagram.regionCount :=
    (input.pattern.val.diagram.climb position.val region).get
      (pathIsSome position)
  have path_spec (position : Fin steps) :
      input.pattern.val.diagram.climb position.val region =
        some (path position) :=
    (Option.some_get (pathIsSome position)).symm
  have path_material (position : Fin steps) :
      input.binderSpine.IsMaterialRegion (path position) :=
    material_of_climb_lt_bodyContainer input steps region (path position)
      position.val hmaterial hclimb position.isLt (path_spec position)
  let pathIndex (position : Fin steps) :
      layout.materialRegions.Carrier :=
    layout.materialIndex (path position) (path_material position)
  have pathIndex_injective : Function.Injective pathIndex := by
    intro first second heq
    have hpaths : path first = path second := by
      have horigins := congrArg layout.materialRegions.origin heq
      simpa only [pathIndex, materialIndex,
        SurvivorDomain.origin_index] using horigins
    obtain ⟨bodyRootSteps, hbodyRoot⟩ :=
      input.pattern.property.diagram_well_formed
        |>.all_regions_reach_root input.binderSpine.bodyContainer
    have hfirstSuffix := splice_climb_cancel_prefix
      (Nat.le_of_lt first.isLt) (path_spec first) hclimb
    have hsecondSuffix := splice_climb_cancel_prefix
      (Nat.le_of_lt second.isLt) (path_spec second) hclimb
    have hfirstRoot := ConcreteElaboration.climb_add hfirstSuffix hbodyRoot
    have hsecondRoot := ConcreteElaboration.climb_add hsecondSuffix hbodyRoot
    rw [hpaths] at hfirstRoot
    have hremaining :=
      ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique
        input.pattern.val.diagram
        input.pattern.property.diagram_well_formed.root_is_sheet
        hfirstRoot hsecondRoot
    apply Fin.ext
    omega
  exact fin_card_le_of_injective pathIndex pathIndex_injective

theorem frame_climb (layout : PlugLayout input) :
    ∀ (steps : Nat) (start finish : Fin input.frame.val.regionCount),
      input.frame.val.climb steps start = some finish →
      layout.plugRaw.climb steps (layout.frameRegion start) =
        some (layout.frameRegion finish) := by
  intro steps
  induction steps with
  | zero =>
      intro start finish hclimb
      have heq : start = finish := Option.some.inj hclimb
      subst finish
      rfl
  | succ steps ih =>
      intro start finish hclimb
      cases hregion : input.frame.val.regions start with
      | sheet =>
          simp [ConcreteDiagram.climb, hregion, CRegion.parent?] at hclimb
      | cut parent =>
          have htail : input.frame.val.climb steps parent = some finish := by
            simpa [ConcreteDiagram.climb, hregion] using hclimb
          simp only [ConcreteDiagram.climb, plugRaw,
            plugRegion_frameRegion, hregion, mapFrameRegion, CRegion.parent?]
          exact ih parent finish htail
      | bubble parent arity =>
          have htail : input.frame.val.climb steps parent = some finish := by
            simpa [ConcreteDiagram.climb, hregion] using hclimb
          simp only [ConcreteDiagram.climb, plugRaw,
            plugRegion_frameRegion, hregion, mapFrameRegion, CRegion.parent?]
          exact ih parent finish htail

theorem plugRaw_all_regions_reach_root (layout : PlugLayout input) :
    layout.plugRaw.AllRegionsReachRoot := by
  intro region
  refine Fin.addCases (m := input.frame.val.regionCount)
    (n := layout.materialRegions.count)
    (fun frame => ?_) (fun material => ?_) region
  · obtain ⟨steps, hframe⟩ :=
      input.frame.property.all_regions_reach_root frame
    refine ⟨⟨steps.val, by
      simp only [plugRaw, regionCount]
      omega⟩, ?_⟩
    exact layout.frame_climb steps.val frame input.frame.val.root hframe
  · let original := layout.materialRegions.origin material
    have hmaterial : input.binderSpine.IsMaterialRegion original :=
      (layout.materialRegions_survives_iff original).1
        (layout.materialRegions.origin_survives material)
    obtain ⟨patternSteps, hpatternRoot⟩ :=
      input.pattern.property.diagram_well_formed.all_regions_reach_root original
    obtain ⟨materialSteps, hmaterialBody, hmaterialSite⟩ :=
      layout.material_climb_body_and_plug_site patternSteps.val original
        hmaterial hpatternRoot
    have hmaterialBound :=
      layout.material_climb_steps_le_count hmaterial hmaterialBody
    obtain ⟨frameSteps, hsiteRoot⟩ :=
      input.frame.property.all_regions_reach_root input.site
    have hframeRoot := layout.frame_climb frameSteps.val input.site
      input.frame.val.root hsiteRoot
    have hplugRoot := ConcreteElaboration.climb_add hmaterialSite hframeRoot
    refine ⟨⟨materialSteps + frameSteps.val, by
      simp only [plugRaw, regionCount]
      omega⟩, ?_⟩
    simpa only [original, layout.bodyRegion_origin material] using hplugRoot

theorem plugRaw_root_is_sheet (layout : PlugLayout input) :
    layout.plugRaw.RootIsSheet := by
  unfold ConcreteDiagram.RootIsSheet
  change layout.plugRegion (layout.frameRegion input.frame.val.root) = .sheet
  rw [layout.plugRegion_frameRegion]
  rw [input.frame.property.root_is_sheet]
  rfl

theorem plugRaw_only_root_is_sheet (layout : PlugLayout input) :
    layout.plugRaw.OnlyRootIsSheet := by
  intro region
  refine Fin.addCases (m := input.frame.val.regionCount)
    (n := layout.materialRegions.count)
    (fun frame => ?_) (fun material => ?_) region
  · intro hsheet
    simp only [plugRaw] at hsheet
    change layout.plugRegion (layout.frameRegion frame) = .sheet at hsheet
    rw [layout.plugRegion_frameRegion frame] at hsheet
    have hframeSheet : input.frame.val.regions frame = .sheet := by
      cases hregion : input.frame.val.regions frame with
      | sheet => rfl
      | cut => simp [hregion, mapFrameRegion] at hsheet
      | bubble => simp [hregion, mapFrameRegion] at hsheet
    have hroot := input.frame.property.only_root_is_sheet frame hframeSheet
    subst frame
    rfl
  · intro hsheet
    simp only [plugRaw] at hsheet
    change layout.plugRegion (layout.materialRegion material) = .sheet at hsheet
    rw [layout.plugRegion_materialRegion material] at hsheet
    have himpossible : layout.mapPatternRegion
        (input.pattern.val.diagram.regions
          (layout.materialRegions.origin material)) ≠ .sheet := by
      cases input.pattern.val.diagram.regions
          (layout.materialRegions.origin material) <;>
        simp [mapPatternRegion]
    exact False.elim (himpossible hsheet)

theorem plugRaw_encloses_trans (layout : PlugLayout input)
    {ancestor middle descendant : Fin layout.plugRaw.regionCount}
    (hfirst : layout.plugRaw.Encloses ancestor middle)
    (hsecond : layout.plugRaw.Encloses middle descendant) :
    layout.plugRaw.Encloses ancestor descendant := by
  obtain ⟨first, hfirst⟩ := hfirst
  obtain ⟨second, hsecond⟩ := hsecond
  obtain ⟨rootSteps, hroot⟩ :=
    layout.plugRaw_all_regions_reach_root ancestor
  have hcomposed := ConcreteElaboration.climb_add hsecond hfirst
  have htoRoot := ConcreteElaboration.climb_add hcomposed hroot
  have hbound :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
      layout.plugRaw layout.plugRaw_root_is_sheet
      layout.plugRaw_all_regions_reach_root htoRoot
  exact ⟨⟨second.val + first.val, by omega⟩, hcomposed⟩

theorem frame_encloses (layout : PlugLayout input)
    {ancestor descendant : Fin input.frame.val.regionCount}
    (hencloses : input.frame.val.Encloses ancestor descendant) :
    layout.plugRaw.Encloses (layout.frameRegion ancestor)
      (layout.frameRegion descendant) := by
  obtain ⟨steps, hsteps⟩ := hencloses
  refine ⟨⟨steps.val, by
    simp only [plugRaw, regionCount]
    omega⟩, layout.frame_climb steps.val descendant ancestor hsteps⟩

theorem site_encloses_bodyRegion (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    layout.plugRaw.Encloses (layout.frameRegion input.site)
      (layout.bodyRegion region) := by
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · obtain ⟨patternSteps, hpatternRoot⟩ :=
      input.pattern.property.diagram_well_formed.all_regions_reach_root region
    obtain ⟨steps, horiginal, hplug⟩ :=
      layout.material_climb_body_and_plug_site patternSteps.val region
        hmaterial hpatternRoot
    have hbound := layout.material_climb_steps_le_count hmaterial horiginal
    refine ⟨⟨steps, by
      simp only [plugRaw, regionCount]
      have := input.frame.val.root.isLt
      omega⟩, hplug⟩
  · rw [layout.bodyRegion_nonmaterial region hmaterial]
    exact ConcreteDiagram.Encloses.refl _ _

theorem material_or_proxy_of_ne_root (input : Input signature)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hneRoot : region ≠ input.pattern.val.diagram.root) :
    input.binderSpine.IsMaterialRegion region ∨
      ∃ index : Fin input.binderSpine.proxyCount,
        region = input.binderSpine.proxy index := by
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · exact Or.inl hmaterial
  · right
    exact Classical.byContradiction fun hnone => hmaterial ⟨hneRoot, by
      intro index heq
      exact hnone ⟨index, heq⟩⟩

theorem plugRaw_binderRegion_isBubble (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (binder parent : Fin input.pattern.val.diagram.regionCount) (arity : Nat)
    (hbubble : input.pattern.val.diagram.regions binder =
      .bubble parent arity) :
    ∃ plugParent, layout.plugRaw.regions (layout.binderRegion binder) =
      .bubble plugParent arity := by
  have hneRoot : binder ≠ input.pattern.val.diagram.root := by
    intro hroot
    rw [hroot, input.pattern.property.diagram_well_formed.root_is_sheet]
      at hbubble
    contradiction
  rcases material_or_proxy_of_ne_root input binder hneRoot with
    hmaterial | ⟨index, hproxy⟩
  · refine ⟨layout.bodyRegion parent, ?_⟩
    change layout.plugRegion (layout.binderRegion binder) = _
    rw [layout.binderRegion_material binder hmaterial,
      layout.bodyRegion_material binder hmaterial,
      layout.plugRegion_materialRegion]
    have horigin : layout.materialRegions.origin
        (layout.materialIndex binder hmaterial) = binder := by
      exact layout.materialRegions.origin_index binder
        ((layout.materialRegions_survives_iff binder).2 hmaterial)
    rw [horigin, hbubble]
    rfl
  · subst binder
    have hproxyRegion := input.binderSpine.proxy_region index
    have harity : input.binderSpine.arity index = arity := by
      rw [hproxyRegion] at hbubble
      cases hbubble
      rfl
    obtain ⟨targetParent, htarget⟩ :=
      hadmissible.binder_targets_match index
    rw [harity] at htarget
    refine ⟨layout.frameRegion targetParent, ?_⟩
    change layout.plugRegion
      (layout.binderRegion (input.binderSpine.proxy index)) = _
    rw [layout.binderRegion_proxy, layout.plugRegion_frameRegion, htarget]
    rfl

theorem plugRaw_atom_binders_are_bubbles (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.AtomBindersAreBubbles := by
  intro node
  refine Fin.addCases (m := input.frame.val.nodeCount)
    (n := input.pattern.val.diagram.nodeCount)
    (fun frameNode => ?_) (fun patternNode => ?_) node
  · have hold := input.frame.property.atom_binders_are_bubbles frameNode
    simp only [plugRaw, plugNode, Fin.addCases_left]
    cases hnode : input.frame.val.nodes frameNode with
    | term => trivial
    | named => trivial
    | atom region binder =>
        simp only [hnode] at hold
        obtain ⟨parent, arity, hbubble⟩ := hold
        refine ⟨layout.frameRegion parent, arity, ?_⟩
        rw [layout.plugRegion_frameRegion, hbubble]
        rfl
  · have hold :=
      input.pattern.property.diagram_well_formed.atom_binders_are_bubbles
        patternNode
    simp only [plugRaw, plugNode, Fin.addCases_right]
    cases hnode : input.pattern.val.diagram.nodes patternNode with
    | term => trivial
    | named => trivial
    | atom region binder =>
        simp only [hnode] at hold
        obtain ⟨parent, arity, hbubble⟩ := hold
        simp only [mapPatternNode]
        obtain ⟨plugParent, hplugBubble⟩ :=
          layout.plugRaw_binderRegion_isBubble
            hadmissible binder parent arity hbubble
        exact ⟨plugParent, arity, hplugBubble⟩

theorem plugRaw_named_references_resolve (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input) :
    layout.plugRaw.NamedReferencesResolve signature := by
  intro node
  refine Fin.addCases (m := input.frame.val.nodeCount)
    (n := input.pattern.val.diagram.nodeCount)
    (fun frameNode => ?_) (fun patternNode => ?_) node
  · have hold := input.frame.property.named_references_resolve frameNode
    simp only [plugRaw, plugNode, Fin.addCases_left]
    cases hnode : input.frame.val.nodes frameNode <;>
      simp only [hnode, mapFrameNode] at hold ⊢
    exact hold
  · have hold :=
      input.pattern.property.diagram_well_formed.named_references_resolve
        patternNode
    simp only [plugRaw, plugNode, Fin.addCases_right]
    cases hnode : input.pattern.val.diagram.nodes patternNode <;>
      simp only [hnode, mapPatternNode] at hold ⊢
    exact hold

theorem bodyContainer_nonmaterial (input : Input signature) :
    ¬ input.binderSpine.IsMaterialRegion
      input.binderSpine.bodyContainer := by
  intro hmaterial
  by_cases hzero : input.binderSpine.proxyCount = 0
  · exact hmaterial.1 (input.binderSpine.body_eq_root_of_empty hzero)
  · rw [input.binderSpine.body_eq_terminal_of_nonempty hzero] at hmaterial
    exact hmaterial.2 _ rfl

theorem bodyRegion_climb_between_material (layout : PlugLayout input) :
    ∀ (steps : Nat)
      (start finish : Fin input.pattern.val.diagram.regionCount),
      input.binderSpine.IsMaterialRegion start →
      input.binderSpine.IsMaterialRegion finish →
      input.pattern.val.diagram.climb steps start = some finish →
      layout.plugRaw.climb steps (layout.bodyRegion start) =
        some (layout.bodyRegion finish) := by
  intro steps
  induction steps with
  | zero =>
      intro start finish _ _ hclimb
      have heq : start = finish := Option.some.inj hclimb
      subst finish
      rfl
  | succ steps ih =>
      intro start finish hstart hfinish hclimb
      cases hparent : (input.pattern.val.diagram.regions start).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hclimb
      | some parent =>
          have htail : input.pattern.val.diagram.climb steps parent =
              some finish := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          have hparentMaterial :
              input.binderSpine.IsMaterialRegion parent := by
            by_cases hcandidate :
                input.binderSpine.IsMaterialRegion parent
            · exact hcandidate
            · have hparentBody := nonmaterial_parent_eq_bodyContainer input
                  start parent hstart hparent hcandidate
              obtain ⟨finishRootSteps, hfinishRoot⟩ :=
                input.pattern.property.diagram_well_formed
                  |>.all_regions_reach_root finish
              obtain ⟨finishBodySteps, hfinishBody, _⟩ :=
                layout.material_climb_body_and_plug_site finishRootSteps.val
                  finish hfinish hfinishRoot
              obtain ⟨bodyRootSteps, hbodyRoot⟩ :=
                input.pattern.property.diagram_well_formed
                  |>.all_regions_reach_root input.binderSpine.bodyContainer
              rw [hparentBody] at htail
              have hcycle := ConcreteElaboration.climb_add htail hfinishBody
              have hcycleRoot := ConcreteElaboration.climb_add hcycle hbodyRoot
              have hunique :=
                ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique
                  input.pattern.val.diagram
                  input.pattern.property.diagram_well_formed.root_is_sheet
                  hcycleRoot hbodyRoot
              have hzero : finishBodySteps = 0 := by omega
              rw [hzero] at hfinishBody
              have hfinishEq := Option.some.inj hfinishBody
              exact False.elim
                (bodyContainer_nonmaterial input (hfinishEq ▸ hfinish))
          have hstep : layout.plugRaw.climb 1
              (layout.bodyRegion start) = some (layout.bodyRegion parent) := by
            simp only [ConcreteDiagram.climb]
            rw [layout.bodyRegion_parent_exact start parent hstart hparent]
            rfl
          have hcombined := ConcreteElaboration.climb_add hstep
            (ih parent finish hparentMaterial hfinish htail)
          simpa [Nat.add_comm] using hcombined

theorem material_encloses (layout : PlugLayout input)
    {ancestor descendant : Fin input.pattern.val.diagram.regionCount}
    (hancestor : input.binderSpine.IsMaterialRegion ancestor)
    (hdescendant : input.binderSpine.IsMaterialRegion descendant)
    (hencloses : input.pattern.val.diagram.Encloses ancestor descendant) :
    layout.plugRaw.Encloses (layout.bodyRegion ancestor)
      (layout.bodyRegion descendant) := by
  obtain ⟨steps, hsteps⟩ := hencloses
  obtain ⟨ancestorRootSteps, hancestorRoot⟩ :=
    input.pattern.property.diagram_well_formed.all_regions_reach_root ancestor
  obtain ⟨ancestorBodySteps, hancestorBody, _⟩ :=
    layout.material_climb_body_and_plug_site ancestorRootSteps.val ancestor
      hancestor hancestorRoot
  have hdescendantBody := ConcreteElaboration.climb_add hsteps hancestorBody
  have hbound :=
    layout.material_climb_steps_le_count hdescendant hdescendantBody
  refine ⟨⟨steps.val, by
    simp only [plugRaw, regionCount]
    have := input.frame.val.root.isLt
    omega⟩, ?_⟩
  exact layout.bodyRegion_climb_between_material steps.val descendant ancestor
    hdescendant hancestor hsteps

theorem patternNode_region_material_or_bodyContainer
    (input : Input signature)
    (node : Fin input.pattern.val.diagram.nodeCount) :
    input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.nodes node).region ∨
      (input.pattern.val.diagram.nodes node).region =
        input.binderSpine.bodyContainer := by
  let region := (input.pattern.val.diagram.nodes node).region
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · exact Or.inl hmaterial
  · right
    by_cases hroot : region = input.pattern.val.diagram.root
    · by_cases hzero : input.binderSpine.proxyCount = 0
      · exact hroot.trans
          (input.binderSpine.body_eq_root_of_empty hzero).symm
      · exact False.elim
          (input.terminalBody.root_has_no_nodes hzero node hroot)
    · obtain ⟨index, hproxy⟩ :=
        (material_or_proxy_of_ne_root input region hroot).resolve_left hmaterial
      by_cases hnonterminal :
          index.val + 1 < input.binderSpine.proxyCount
      · exact False.elim
          (input.terminalBody.nonterminal_has_no_nodes
            index hnonterminal node hproxy)
      · have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
          have := index.isLt
          omega
        let terminal : Fin input.binderSpine.proxyCount :=
          ⟨input.binderSpine.proxyCount - 1, by omega⟩
        have hterminal : index = terminal := by
          apply Fin.ext
          simp only [terminal]
          have := index.isLt
          omega
        change region = input.binderSpine.bodyContainer
        rw [hproxy, hterminal]
        exact (input.binderSpine.body_eq_terminal_of_nonempty hnonzero).symm

theorem material_not_encloses_bodyContainer (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    ¬ input.pattern.val.diagram.Encloses region
      input.binderSpine.bodyContainer := by
  intro hencloses
  obtain ⟨upSteps, hup⟩ := hencloses
  obtain ⟨rootSteps, hroot⟩ :=
    input.pattern.property.diagram_well_formed.all_regions_reach_root region
  obtain ⟨downSteps, hdown, _⟩ :=
    layout.material_climb_body_and_plug_site rootSteps.val region
      hmaterial hroot
  obtain ⟨bodyRootSteps, hbodyRoot⟩ :=
    input.pattern.property.diagram_well_formed.all_regions_reach_root
      input.binderSpine.bodyContainer
  have hcycle := ConcreteElaboration.climb_add hup hdown
  have hcycleRoot := ConcreteElaboration.climb_add hcycle hbodyRoot
  have hunique :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique
      input.pattern.val.diagram
      input.pattern.property.diagram_well_formed.root_is_sheet
      hcycleRoot hbodyRoot
  have hupZero : upSteps.val = 0 := by omega
  rw [hupZero] at hup
  have heq := Option.some.inj hup
  exact bodyContainer_nonmaterial input (heq ▸ hmaterial)

theorem plugRaw_atom_binders_enclose (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.AtomBindersEnclose := by
  intro node
  refine Fin.addCases (m := input.frame.val.nodeCount)
    (n := input.pattern.val.diagram.nodeCount)
    (fun frameNode => ?_) (fun patternNode => ?_) node
  · have hold := input.frame.property.atom_binders_enclose frameNode
    simp only [plugRaw, plugNode, Fin.addCases_left]
    cases hnode : input.frame.val.nodes frameNode with
    | term => trivial
    | named => trivial
    | atom region binder =>
        simp only [hnode] at hold
        simp only [mapFrameNode]
        exact layout.frame_encloses hold
  · have hold :=
      input.pattern.property.diagram_well_formed.atom_binders_enclose
        patternNode
    simp only [plugRaw, plugNode, Fin.addCases_right]
    cases hnode : input.pattern.val.diagram.nodes patternNode with
    | term => trivial
    | named => trivial
    | atom region binder =>
        simp only [hnode] at hold
        simp only [mapPatternNode]
        have hbinderBubble :=
          input.pattern.property.diagram_well_formed.atom_binders_are_bubbles
            patternNode
        simp only [hnode] at hbinderBubble
        obtain ⟨parent, arity, hbubble⟩ := hbinderBubble
        have hneRoot : binder ≠ input.pattern.val.diagram.root := by
          intro hroot
          rw [hroot,
            input.pattern.property.diagram_well_formed.root_is_sheet] at hbubble
          contradiction
        rcases material_or_proxy_of_ne_root input binder hneRoot with
          hmaterial | ⟨index, hproxy⟩
        · rw [layout.binderRegion_material binder hmaterial]
          have howner :=
            patternNode_region_material_or_bodyContainer input patternNode
          simp only [hnode, CNode.region] at howner
          rcases howner with
            hregionMaterial | hregionBody
          · exact layout.material_encloses hmaterial hregionMaterial hold
          · rw [hregionBody] at hold
            exact False.elim (layout.material_not_encloses_bodyContainer
              binder hmaterial hold)
        · subst binder
          rw [layout.binderRegion_proxy]
          have htarget := layout.frame_encloses
            (hadmissible.binder_targets_enclose index)
          exact layout.plugRaw_encloses_trans htarget
            (layout.site_encloses_bodyRegion region)

theorem plugRaw_requiresPort_frame (layout : PlugLayout input)
    (node : Fin input.frame.val.nodeCount) (port : CPort)
    (hrequires : input.frame.val.RequiresPort node port) :
    layout.plugRaw.RequiresPort (layout.frameNode node) port := by
  unfold ConcreteDiagram.RequiresPort at hrequires ⊢
  simp only [plugRaw]
  rw [layout.plugNode_frameNode]
  cases hnode : input.frame.val.nodes node with
  | term => simpa only [hnode, mapFrameNode] using hrequires
  | named => simpa only [hnode, mapFrameNode] using hrequires
  | atom region binder =>
      simp only [hnode, mapFrameNode] at hrequires ⊢
      rw [layout.plugRegion_frameRegion]
      cases hbinder : input.frame.val.regions binder <;>
        simp [hbinder, mapFrameRegion] at hrequires ⊢
      exact hrequires

theorem plugRaw_requiresPort_pattern (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (node : Fin input.pattern.val.diagram.nodeCount) (port : CPort)
    (hrequires : input.pattern.val.diagram.RequiresPort node port) :
    layout.plugRaw.RequiresPort (layout.patternNode node) port := by
  unfold ConcreteDiagram.RequiresPort at hrequires ⊢
  simp only [plugRaw]
  rw [layout.plugNode_patternNode]
  cases hnode : input.pattern.val.diagram.nodes node with
  | term => simpa only [hnode, mapPatternNode] using hrequires
  | named => simpa only [hnode, mapPatternNode] using hrequires
  | atom region binder =>
      simp only [hnode, mapPatternNode] at hrequires ⊢
      cases hbinder : input.pattern.val.diagram.regions binder with
      | sheet => simp [hbinder] at hrequires
      | cut => simp [hbinder] at hrequires
      | bubble parent arity =>
          obtain ⟨plugParent, hplug⟩ :=
            layout.plugRaw_binderRegion_isBubble hadmissible binder parent
              arity hbinder
          change layout.plugRegion (layout.binderRegion binder) = _ at hplug
          rw [hplug]
          simpa only [hbinder] using hrequires

theorem plugRaw_endpoints_are_valid (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.EndpointsAreValid := by
  intro wire
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count)
    (fun quotient => ?_) (fun internal => ?_) wire
  · intro endpoint hendpoint
    change CEndpoint layout.nodeCount at endpoint
    simp only [plugRaw, plugWire, Fin.addCases_left] at hendpoint
    rcases List.mem_append.mp hendpoint with hframe | hboundary
    · obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hframe
      rw [input.mem_coalescedEndpoints] at horiginal
      obtain ⟨sourceWire, _, hsource⟩ := horiginal
      exact layout.plugRaw_requiresPort_frame original.node original.port
        (input.frame.property.endpoints_are_valid
          sourceWire original hsource)
    · rw [layout.mem_boundaryEndpoints] at hboundary
      obtain ⟨external, _, original, horiginal, rfl⟩ := hboundary
      exact layout.plugRaw_requiresPort_pattern hadmissible
        original.node original.port
        (input.pattern.property.diagram_well_formed.endpoints_are_valid
          (input.pattern.val.exposedWires.get external) original horiginal)
  · intro endpoint hendpoint
    change CEndpoint layout.nodeCount at endpoint
    simp only [plugRaw, plugWire, Fin.addCases_right, mapPatternWire] at hendpoint
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hendpoint
    exact layout.plugRaw_requiresPort_pattern hadmissible
      original.node original.port
      (input.pattern.property.diagram_well_formed.endpoints_are_valid
        (layout.internalWires.origin internal) original horiginal)

theorem plugRaw_endpointOccurs_frame (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (wire : Fin input.frame.val.wireCount)
    (endpoint : CEndpoint input.frame.val.nodeCount)
    (hoccurs : input.frame.val.EndpointOccurs wire endpoint) :
    layout.plugRaw.EndpointOccurs
      (layout.quotientBlockWire (input.quotientWire wire))
      (layout.mapFrameEndpoint endpoint) := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [plugRaw]
  rw [plugWire_quotientBlockWire signature input layout]
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨endpoint, ?_, rfl⟩
  rw [input.mem_coalescedEndpoints]
  exact ⟨wire, (input.mem_classWires _ wire).2 rfl, hoccurs⟩

theorem plugRaw_endpointOccurs_pattern (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount)
    (hoccurs : input.pattern.val.diagram.EndpointOccurs wire endpoint) :
    ∃ plugWire, layout.plugRaw.EndpointOccurs plugWire
      (layout.mapPatternEndpoint endpoint) := by
  change endpoint ∈ (input.pattern.val.diagram.wires wire).endpoints at hoccurs
  by_cases hexposed : wire ∈ input.pattern.val.exposedWires
  · obtain ⟨external, hexternal⟩ := indexOf?_complete hexposed
    have hget := indexOf?_sound hexternal
    refine ⟨layout.quotientBlockWire (layout.exposedAttachment external), ?_⟩
    unfold ConcreteDiagram.EndpointOccurs
    simp only [plugRaw]
    rw [plugWire_quotientBlockWire signature input layout]
    apply List.mem_append_right
    rw [layout.mem_boundaryEndpoints]
    refine ⟨external, rfl, endpoint, ?_, rfl⟩
    have hget' : input.pattern.val.exposedWires.get external = wire := by
      simpa only [List.get_eq_getElem] using hget
    rw [hget']
    exact hoccurs
  · let internal := layout.internalWires.index wire
        ((layout.internalWires_survives_iff wire).2 hexposed)
    refine ⟨layout.internalBlockWire internal, ?_⟩
    unfold ConcreteDiagram.EndpointOccurs
    simp only [plugRaw]
    rw [plugWire_internalBlockWire signature input layout]
    change layout.mapPatternEndpoint endpoint ∈
      (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal)).endpoints.map
          layout.mapPatternEndpoint
    have horigin : layout.internalWires.origin internal = wire := by
      exact layout.internalWires.origin_index wire
        ((layout.internalWires_survives_iff wire).2 hexposed)
    rw [horigin]
    exact List.mem_map.mpr ⟨endpoint, hoccurs, rfl⟩

theorem plugRaw_required_ports_are_covered (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.RequiredPortsAreCovered := by
  intro node
  refine Fin.addCases (m := input.frame.val.nodeCount)
    (n := input.pattern.val.diagram.nodeCount)
    (fun frameNode => ?_) (fun patternNode => ?_) node
  · have hold := input.frame.property.required_ports_are_covered frameNode
    simp only [plugRaw, plugNode, Fin.addCases_left]
    cases hnode : input.frame.val.nodes frameNode with
    | term region freePorts term =>
        simp only [hnode, mapFrameNode] at hold ⊢
        obtain ⟨outputWire, houtput⟩ := hold.1
        refine ⟨⟨layout.quotientBlockWire
          (input.quotientWire outputWire), ?_⟩, ?_⟩
        · simpa [mapFrameEndpoint] using
            plugRaw_endpointOccurs_frame signature input layout
              outputWire ⟨frameNode, .output⟩ houtput
        · intro index
          obtain ⟨sourceWire, hsource⟩ := hold.2 index
          refine ⟨layout.quotientBlockWire
            (input.quotientWire sourceWire), ?_⟩
          simpa [mapFrameEndpoint] using
            plugRaw_endpointOccurs_frame signature input layout
              sourceWire ⟨frameNode, .free index⟩ hsource
    | named region definition arity =>
        simp only [hnode, mapFrameNode] at hold ⊢
        intro index
        obtain ⟨sourceWire, hsource⟩ := hold index
        refine ⟨layout.quotientBlockWire
          (input.quotientWire sourceWire), ?_⟩
        simpa [mapFrameEndpoint] using
          plugRaw_endpointOccurs_frame signature input layout
            sourceWire ⟨frameNode, .arg index⟩ hsource
    | atom region binder =>
        simp only [hnode, mapFrameNode] at hold ⊢
        rw [layout.plugRegion_frameRegion]
        cases hbinder : input.frame.val.regions binder with
        | sheet => trivial
        | cut => trivial
        | bubble parent arity =>
            simp only [hbinder, mapFrameRegion] at hold ⊢
            intro index
            obtain ⟨sourceWire, hsource⟩ := hold index
            refine ⟨layout.quotientBlockWire
              (input.quotientWire sourceWire), ?_⟩
            simpa [mapFrameEndpoint] using
              plugRaw_endpointOccurs_frame signature input layout
                sourceWire ⟨frameNode, .arg index⟩ hsource
  · have hold :=
      input.pattern.property.diagram_well_formed.required_ports_are_covered
        patternNode
    simp only [plugRaw, plugNode, Fin.addCases_right]
    cases hnode : input.pattern.val.diagram.nodes patternNode with
    | term region freePorts term =>
        simp only [hnode, mapPatternNode] at hold ⊢
        obtain ⟨outputWire, houtput⟩ := hold.1
        obtain ⟨plugOutput, hplugOutput⟩ :=
          plugRaw_endpointOccurs_pattern signature input layout outputWire
            ⟨patternNode, .output⟩ houtput
        refine ⟨⟨plugOutput, by
          simpa [mapPatternEndpoint] using hplugOutput⟩, ?_⟩
        intro index
        obtain ⟨sourceWire, hsource⟩ := hold.2 index
        obtain ⟨plugWire, hplug⟩ :=
          plugRaw_endpointOccurs_pattern signature input layout sourceWire
            ⟨patternNode, .free index⟩ hsource
        exact ⟨plugWire, by simpa [mapPatternEndpoint] using hplug⟩
    | named region definition arity =>
        simp only [hnode, mapPatternNode] at hold ⊢
        intro index
        obtain ⟨sourceWire, hsource⟩ := hold index
        obtain ⟨plugWire, hplug⟩ :=
          plugRaw_endpointOccurs_pattern signature input layout sourceWire
            ⟨patternNode, .arg index⟩ hsource
        exact ⟨plugWire, by simpa [mapPatternEndpoint] using hplug⟩
    | atom region binder =>
        simp only [hnode, mapPatternNode] at hold ⊢
        have hbinder :=
          input.pattern.property.diagram_well_formed.atom_binders_are_bubbles
            patternNode
        simp only [hnode] at hbinder
        obtain ⟨parent, arity, hbubble⟩ := hbinder
        obtain ⟨plugParent, hplugBubble⟩ :=
          layout.plugRaw_binderRegion_isBubble hadmissible
            binder parent arity hbubble
        change layout.plugRegion (layout.binderRegion binder) = _ at hplugBubble
        rw [hplugBubble]
        simp only [hbubble] at hold
        intro index
        obtain ⟨sourceWire, hsource⟩ := hold index
        obtain ⟨plugWire, hplug⟩ :=
          plugRaw_endpointOccurs_pattern signature input layout sourceWire
            ⟨patternNode, .arg index⟩ hsource
        exact ⟨plugWire, by simpa [mapPatternEndpoint] using hplug⟩

theorem plugRaw_endpoints_are_nodup (layout : PlugLayout input) :
    layout.plugRaw.EndpointsAreNodup := by
  intro wire
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count)
    (fun quotient => ?_) (fun internal => ?_) wire
  · simp only [plugRaw, plugWire, Fin.addCases_left]
    rw [List.nodup_append]
    refine ⟨?_, layout.boundaryEndpoints_nodup quotient, ?_⟩
    · apply List.Pairwise.map
        (R := fun left right => left ≠ right)
        (S := fun left right => left ≠ right)
        layout.mapFrameEndpoint
        (fun left right hne heq => hne
          (layout.mapFrameEndpoint_injective heq))
      exact input.coalescedEndpoints_nodup quotient
    · intro frameEndpoint hframe patternEndpoint hpattern heq
      obtain ⟨frameOriginal, _, rfl⟩ := List.mem_map.mp hframe
      rw [layout.mem_boundaryEndpoints] at hpattern
      obtain ⟨_, _, patternOriginal, _, hpatternEq⟩ := hpattern
      exact layout.mapFrameEndpoint_ne_mapPatternEndpoint
        frameOriginal patternOriginal (heq.trans hpatternEq.symm)
  · simp only [plugRaw, plugWire, Fin.addCases_right, mapPatternWire]
    apply List.Pairwise.map
      (R := fun left right => left ≠ right)
      (S := fun left right => left ≠ right)
      layout.mapPatternEndpoint
      (fun left right hne heq => hne
        (layout.mapPatternEndpoint_injective heq))
    exact input.pattern.property.diagram_well_formed.endpoints_are_nodup
      (layout.internalWires.origin internal)

theorem patternWire_scope_material_or_bodyContainer
    (input : Input signature)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (hinternal : wire ∉ input.pattern.val.exposedWires) :
    input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.wires wire).scope ∨
      (input.pattern.val.diagram.wires wire).scope =
        input.binderSpine.bodyContainer := by
  let region := (input.pattern.val.diagram.wires wire).scope
  have hnotBoundary : wire ∉ input.pattern.val.boundary := by
    intro hboundary
    exact hinternal ((input.pattern.val.mem_exposedWires wire).2 hboundary)
  by_cases hmaterial : input.binderSpine.IsMaterialRegion region
  · exact Or.inl hmaterial
  · right
    by_cases hroot : region = input.pattern.val.diagram.root
    · by_cases hzero : input.binderSpine.proxyCount = 0
      · exact hroot.trans
          (input.binderSpine.body_eq_root_of_empty hzero).symm
      · exact False.elim
          (input.terminalBody.root_has_no_nonboundary_wires
            hzero wire hnotBoundary hroot)
    · obtain ⟨index, hproxy⟩ :=
        (material_or_proxy_of_ne_root input region hroot).resolve_left hmaterial
      by_cases hnonterminal :
          index.val + 1 < input.binderSpine.proxyCount
      · exact False.elim
          (input.terminalBody.nonterminal_has_no_nonboundary_wires
            index hnonterminal wire hnotBoundary hproxy)
      · have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
          have := index.isLt
          omega
        let terminal : Fin input.binderSpine.proxyCount :=
          ⟨input.binderSpine.proxyCount - 1, by omega⟩
        have hterminal : index = terminal := by
          apply Fin.ext
          simp only [terminal]
          have := index.isLt
          omega
        change region = input.binderSpine.bodyContainer
        rw [hproxy, hterminal]
        exact (input.binderSpine.body_eq_terminal_of_nonempty hnonzero).symm

theorem bodyRegion_encloses_of_owners (layout : PlugLayout input)
    (scope region : Fin input.pattern.val.diagram.regionCount)
    (hscope : input.binderSpine.IsMaterialRegion scope ∨
      scope = input.binderSpine.bodyContainer)
    (hregion : input.binderSpine.IsMaterialRegion region ∨
      region = input.binderSpine.bodyContainer)
    (hencloses : input.pattern.val.diagram.Encloses scope region) :
    layout.plugRaw.Encloses (layout.bodyRegion scope)
      (layout.bodyRegion region) := by
  rcases hscope with hscopeMaterial | rfl
  · rcases hregion with hregionMaterial | hregionBody
    · exact layout.material_encloses
        hscopeMaterial hregionMaterial hencloses
    · rw [hregionBody] at hencloses
      exact False.elim (layout.material_not_encloses_bodyContainer
        scope hscopeMaterial hencloses)
  · rw [layout.bodyRegion_bodyContainer]
    exact layout.site_encloses_bodyRegion region

theorem plugRaw_wire_scopes_enclose (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.WireScopesEnclose := by
  intro wire
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count)
    (fun quotient => ?_) (fun internal => ?_) wire
  · intro endpoint hendpoint
    change CEndpoint layout.nodeCount at endpoint
    unfold ConcreteDiagram.EndpointOccurs at hendpoint
    simp only [plugRaw, plugWire, Fin.addCases_left] at hendpoint
    simp only [plugRaw, plugWire, Fin.addCases_left] at ⊢
    rcases List.mem_append.mp hendpoint with hframe | hboundary
    · obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hframe
      rw [input.mem_coalescedEndpoints] at horiginal
      obtain ⟨sourceWire, hclass, hsource⟩ := horiginal
      have houter := input.coalescedScope_encloses_member
        hadmissible quotient sourceWire hclass
      have hsourceScope := input.frame.property.wire_scopes_enclose
        sourceWire original hsource
      simpa [mapFrameEndpoint, plugRaw] using
        layout.frame_encloses
          (ConcreteElaboration.checked_encloses_trans input.frame.property
            houter hsourceScope)
    · rw [layout.mem_boundaryEndpoints] at hboundary
      obtain ⟨external, hattachment, original, horiginal, rfl⟩ := hboundary
      let attached := input.attachment (layout.exposedPosition external)
      have hclass : attached ∈ input.classWires quotient := by
        rw [input.mem_classWires]
        exact hattachment
      have houter := input.coalescedScope_encloses_member
        hadmissible quotient attached hclass
      have hvisible := hadmissible.attachments_visible
        (layout.exposedPosition external)
      have hscopeSite := ConcreteElaboration.checked_encloses_trans
        input.frame.property houter hvisible
      simpa [mapPatternEndpoint, plugRaw] using
        layout.plugRaw_encloses_trans (layout.frame_encloses hscopeSite)
          (layout.site_encloses_bodyRegion
            (input.pattern.val.diagram.nodes original.node).region)
  · intro endpoint hendpoint
    change CEndpoint layout.nodeCount at endpoint
    unfold ConcreteDiagram.EndpointOccurs at hendpoint
    simp only [plugRaw, plugWire, Fin.addCases_right, mapPatternWire]
      at hendpoint
    simp only [plugRaw, plugWire, Fin.addCases_right, mapPatternWire] at ⊢
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hendpoint
    let sourceWire := layout.internalWires.origin internal
    have hinternal : sourceWire ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff sourceWire).1
        (layout.internalWires.origin_survives internal)
    have hscopeOwner := patternWire_scope_material_or_bodyContainer
      input sourceWire hinternal
    have hregionOwner := patternNode_region_material_or_bodyContainer
      input original.node
    have horiginalScope :=
      input.pattern.property.diagram_well_formed.wire_scopes_enclose
        sourceWire original horiginal
    simpa [mapPatternEndpoint, plugRaw, sourceWire] using
      layout.bodyRegion_encloses_of_owners
        (input.pattern.val.diagram.wires sourceWire).scope
        (input.pattern.val.diagram.nodes original.node).region
        hscopeOwner hregionOwner horiginalScope

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
