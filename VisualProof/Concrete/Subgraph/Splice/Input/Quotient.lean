import VisualProof.Concrete.Subgraph.Decomposition

namespace VisualProof.Data.Finite.FinitePartition

open VisualProof.Concrete

def quotientDomain (partition : FinitePartition size) : SurvivorDomain size where
  survives index := decide (partition.representative index = index)

@[simp] theorem quotientDomain_survives_iff
    (partition : FinitePartition size) (index : Fin size) :
    partition.quotientDomain.survives index = true ↔
      partition.representative index = index := by
  simp [quotientDomain]

def classIndex (partition : FinitePartition size)
    (normalized : partition.Normalized) (index : Fin size) :
    partition.quotientDomain.Carrier :=
  partition.quotientDomain.index (partition.representative index) (by
    rw [quotientDomain_survives_iff]
    exact normalized index)

@[simp] theorem quotientOrigin_classIndex
    (partition : FinitePartition size) (normalized : partition.Normalized)
    (index : Fin size) :
    partition.quotientDomain.origin (partition.classIndex normalized index) =
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
    have horigin := congrArg partition.quotientDomain.origin heq
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
  exact (quotientDomain_survives_iff partition _).1
    (partition.quotientDomain.origin_survives quotient)

end VisualProof.Data.Finite.FinitePartition

namespace VisualProof.Concrete.Splice

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

/-- Proof-free inputs to checked concrete replacement. -/
structure Input where
  frame : Checked
  pattern : CheckedOpen
  site : Fin frame.val.regionCount
  attachment : Fin pattern.val.boundary.length → Fin frame.val.wireCount
  binderSpine : BinderSpine pattern.val.diagram
  binderTarget : Fin binderSpine.proxyCount → Fin frame.val.regionCount

namespace Input

private def terminalRootDirectDecidable (pattern : CheckedOpen)
    (spine : BinderSpine pattern.val.diagram) : Decidable
      (∀ hnonzero : spine.proxyCount ≠ 0, ∀ region,
        (pattern.val.diagram.regions region).parent? =
            some pattern.val.diagram.root →
          region = spine.proxy ⟨0, Nat.pos_of_ne_zero hnonzero⟩) := by
  by_cases hzero : spine.proxyCount = 0
  · exact isTrue (by intro nonzero; contradiction)
  · let first : Fin spine.proxyCount := ⟨0, Nat.pos_of_ne_zero hzero⟩
    letI : Decidable (∀ region,
        (pattern.val.diagram.regions region).parent? =
            some pattern.val.diagram.root → region = spine.proxy first) :=
      inferInstance
    exact decidable_of_iff
      (∀ region, (pattern.val.diagram.regions region).parent? =
          some pattern.val.diagram.root → region = spine.proxy first) (by
        constructor
        · intro direct _ region parent
          exact direct region parent
        · intro contract region parent
          exact contract hzero region parent)

private def terminalNonterminalDirectDecidable (pattern : CheckedOpen)
    (spine : BinderSpine pattern.val.diagram) : Decidable
      (∀ (proxy : Fin spine.proxyCount)
        (hnonterminal : proxy.val + 1 < spine.proxyCount), ∀ region,
          (pattern.val.diagram.regions region).parent? =
              some (spine.proxy proxy) →
            region = spine.proxy ⟨proxy.val + 1, hnonterminal⟩) := by
  exact @Nat.decidableForallFin _ _ fun proxy => by
    by_cases hnext : proxy.val + 1 < spine.proxyCount
    · let next : Fin spine.proxyCount := ⟨proxy.val + 1, hnext⟩
      letI : Decidable (∀ region,
          (pattern.val.diagram.regions region).parent? =
              some (spine.proxy proxy) → region = spine.proxy next) :=
        inferInstance
      exact decidable_of_iff
        (∀ region, (pattern.val.diagram.regions region).parent? =
            some (spine.proxy proxy) → region = spine.proxy next) (by
          constructor
          · intro direct _ region parent
            exact direct region parent
          · intro contract region parent
            exact contract hnext region parent)
    · exact isTrue (by intro impossible; exact (hnext impossible).elim)

private def terminalRootNoNodesDecidable (pattern : CheckedOpen)
    (spine : BinderSpine pattern.val.diagram) : Decidable
      (spine.proxyCount ≠ 0 → ∀ node,
        (pattern.val.diagram.nodes node).region ≠ pattern.val.diagram.root) := by
  by_cases hzero : spine.proxyCount = 0
  · exact isTrue (by intro nonzero; contradiction)
  · letI : Decidable (∀ node,
        (pattern.val.diagram.nodes node).region ≠ pattern.val.diagram.root) :=
      inferInstance
    exact decidable_of_iff
      (∀ node, (pattern.val.diagram.nodes node).region ≠
        pattern.val.diagram.root) (by
          constructor
          · intro noNodes _ node
            exact noNodes node
          · intro contract node
            exact contract hzero node)

private def terminalNonterminalNoNodesDecidable (pattern : CheckedOpen)
    (spine : BinderSpine pattern.val.diagram) : Decidable
      (∀ (proxy : Fin spine.proxyCount), proxy.val + 1 < spine.proxyCount →
        ∀ node, (pattern.val.diagram.nodes node).region ≠ spine.proxy proxy) := by
  exact @Nat.decidableForallFin _ _ fun proxy => by
    by_cases hnext : proxy.val + 1 < spine.proxyCount
    · letI : Decidable (∀ node,
          (pattern.val.diagram.nodes node).region ≠ spine.proxy proxy) :=
        inferInstance
      exact decidable_of_iff
        (∀ node, (pattern.val.diagram.nodes node).region ≠
          spine.proxy proxy) (by
          constructor
          · intro noNodes _ node
            exact noNodes node
          · intro contract node
            exact contract hnext node)
    · exact isTrue (by intro impossible; exact (hnext impossible).elim)

private def terminalRootNoWiresDecidable (pattern : CheckedOpen)
    (spine : BinderSpine pattern.val.diagram) : Decidable
      (spine.proxyCount ≠ 0 → ∀ wire, wire ∉ pattern.val.boundary →
        (pattern.val.diagram.wires wire).scope ≠ pattern.val.diagram.root) := by
  by_cases hzero : spine.proxyCount = 0
  · exact isTrue (by intro nonzero; contradiction)
  · letI : Decidable (∀ wire, wire ∉ pattern.val.boundary →
        (pattern.val.diagram.wires wire).scope ≠ pattern.val.diagram.root) :=
      inferInstance
    exact decidable_of_iff
      (∀ wire, wire ∉ pattern.val.boundary →
        (pattern.val.diagram.wires wire).scope ≠ pattern.val.diagram.root) (by
          constructor
          · intro noWires _ wire boundary
            exact noWires wire boundary
          · intro contract wire boundary
            exact contract hzero wire boundary)

private def terminalNonterminalNoWiresDecidable (pattern : CheckedOpen)
    (spine : BinderSpine pattern.val.diagram) : Decidable
      (∀ (proxy : Fin spine.proxyCount), proxy.val + 1 < spine.proxyCount →
        ∀ wire, wire ∉ pattern.val.boundary →
          (pattern.val.diagram.wires wire).scope ≠ spine.proxy proxy) := by
  exact @Nat.decidableForallFin _ _ fun proxy => by
    by_cases hnext : proxy.val + 1 < spine.proxyCount
    · letI : Decidable (∀ wire, wire ∉ pattern.val.boundary →
          (pattern.val.diagram.wires wire).scope ≠ spine.proxy proxy) :=
        inferInstance
      exact decidable_of_iff
        (∀ wire, wire ∉ pattern.val.boundary →
          (pattern.val.diagram.wires wire).scope ≠ spine.proxy proxy) (by
          constructor
          · intro noWires _ wire boundary
            exact noWires wire boundary
          · intro contract wire boundary
            exact contract hnext wire boundary)
    · exact isTrue (by intro impossible; exact (hnext impossible).elim)

/-- The designated proxy prefix reaches one terminal body, with no ordinary
content stranded at the fresh root or at a nonterminal proxy. -/
def TerminalBody (input : Input) : Prop :=
  input.binderSpine.TerminalBodyContract input.pattern.val

instance (input : Input) : Decidable input.TerminalBody := by
  letI := terminalRootDirectDecidable input.pattern input.binderSpine
  letI := terminalNonterminalDirectDecidable input.pattern input.binderSpine
  letI := terminalRootNoNodesDecidable input.pattern input.binderSpine
  letI := terminalNonterminalNoNodesDecidable input.pattern input.binderSpine
  letI := terminalRootNoWiresDecidable input.pattern input.binderSpine
  letI := terminalNonterminalNoWiresDecidable input.pattern input.binderSpine
  unfold TerminalBody
  by_cases hrootDirect : ∀ hnonzero : input.binderSpine.proxyCount ≠ 0,
      ∀ region, (input.pattern.val.diagram.regions region).parent? =
          some input.pattern.val.diagram.root →
        region = input.binderSpine.proxy
          ⟨0, Nat.pos_of_ne_zero hnonzero⟩
  · by_cases hnonterminalDirect :
        ∀ (proxy : Fin input.binderSpine.proxyCount)
          (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount),
          ∀ region, (input.pattern.val.diagram.regions region).parent? =
              some (input.binderSpine.proxy proxy) →
            region = input.binderSpine.proxy
              ⟨proxy.val + 1, hnonterminal⟩
    · by_cases hrootNodes : input.binderSpine.proxyCount ≠ 0 → ∀ node,
          (input.pattern.val.diagram.nodes node).region ≠
            input.pattern.val.diagram.root
      · by_cases hnonterminalNodes :
            ∀ (proxy : Fin input.binderSpine.proxyCount),
              proxy.val + 1 < input.binderSpine.proxyCount → ∀ node,
                (input.pattern.val.diagram.nodes node).region ≠
                  input.binderSpine.proxy proxy
        · by_cases hrootWires : input.binderSpine.proxyCount ≠ 0 →
              ∀ wire, wire ∉ input.pattern.val.boundary →
                (input.pattern.val.diagram.wires wire).scope ≠
                  input.pattern.val.diagram.root
          · by_cases hnonterminalWires :
                ∀ (proxy : Fin input.binderSpine.proxyCount),
                  proxy.val + 1 < input.binderSpine.proxyCount → ∀ wire,
                    wire ∉ input.pattern.val.boundary →
                      (input.pattern.val.diagram.wires wire).scope ≠
                        input.binderSpine.proxy proxy
            · exact isTrue {
                root_direct_child := hrootDirect
                nonterminal_direct_child := hnonterminalDirect
                root_has_no_nodes := hrootNodes
                nonterminal_has_no_nodes := hnonterminalNodes
                root_has_no_nonboundary_wires := hrootWires
                nonterminal_has_no_nonboundary_wires := hnonterminalWires
                boundary_is_root_scoped :=
                  input.pattern.property.boundary_is_root_scoped
              }
            · exact isFalse fun contract =>
                hnonterminalWires contract.nonterminal_has_no_nonboundary_wires
          · exact isFalse fun contract =>
              hrootWires contract.root_has_no_nonboundary_wires
        · exact isFalse fun contract =>
            hnonterminalNodes contract.nonterminal_has_no_nodes
      · exact isFalse fun contract => hrootNodes contract.root_has_no_nodes
    · exact isFalse fun contract =>
        hnonterminalDirect contract.nonterminal_direct_child
  · exact isFalse fun contract => hrootDirect contract.root_direct_child

/-- Boundary-position equations; equal pattern-wire identities alone generate them. -/
def attachmentEdges (input : Input ) :
    List (Fin input.frame.val.wireCount × Fin input.frame.val.wireCount) :=
  (allFin input.pattern.val.boundary.length).flatMap fun left =>
    (allFin input.pattern.val.boundary.length).filterMap fun right =>
      if input.pattern.val.boundary.get left =
          input.pattern.val.boundary.get right then
        some (input.attachment left, input.attachment right)
      else
        none

/-- A contextual insertion may identify repeated boundary positions only when
those positions already name the same frame wire.  This source-only contract
separates logical insertion from the more general raw splice operation, which
also supports intentional frame-wire coalescence. -/
def AttachmentConsistent (input : Input) : Prop :=
  ∀ left right : Fin input.pattern.val.boundary.length,
    input.pattern.val.boundary.get left =
        input.pattern.val.boundary.get right →
      input.attachment left = input.attachment right

instance (input : Input) : Decidable input.AttachmentConsistent := by
  unfold AttachmentConsistent
  infer_instance

theorem mem_attachmentEdges_iff (input : Input )
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

theorem attachmentEdge_eq (input : Input)
    (consistent : input.AttachmentConsistent)
    {edge : Fin input.frame.val.wireCount × Fin input.frame.val.wireCount}
    (member : edge ∈ input.attachmentEdges) : edge.1 = edge.2 := by
  rw [input.mem_attachmentEdges_iff] at member
  obtain ⟨left, right, boundaryEq, rfl⟩ := member
  exact consistent left right boundaryEq

def attachmentPartition (input : Input ) :
    FinitePartition input.frame.val.wireCount :=
  FinitePartition.ofEdges input.attachmentEdges

theorem attachmentPartition_normalized (input : Input ) :
    input.attachmentPartition.Normalized :=
  FinitePartition.ofEdges_normalized input.attachmentEdges

def wireQuotient (input : Input ) :
    SurvivorDomain input.frame.val.wireCount :=
  input.attachmentPartition.quotientDomain

def quotientWire (input : Input )
    (wire : Fin input.frame.val.wireCount) : input.wireQuotient.Carrier :=
  input.attachmentPartition.classIndex
    input.attachmentPartition_normalized wire

theorem quotientWire_eq_iff (input : Input )
    (left right : Fin input.frame.val.wireCount) :
    input.quotientWire left = input.quotientWire right ↔
      input.attachmentPartition.related left right = true :=
  input.attachmentPartition.classIndex_eq_iff_related
    input.attachmentPartition_normalized left right

theorem attachmentPartition_related_eq (input : Input)
    (consistent : input.AttachmentConsistent)
    {left right : Fin input.frame.val.wireCount}
    (related : input.attachmentPartition.related left right = true) :
    left = right := by
  exact FinitePartition.least (relation := fun first second => first = second)
    (fun _ => rfl) (fun equality => equality.symm)
    (fun first second => first.trans second)
    (fun edge member => input.attachmentEdge_eq consistent member) related

theorem quotientWire_injective (input : Input)
    (consistent : input.AttachmentConsistent) :
    Function.Injective input.quotientWire := by
  intro left right equality
  apply input.attachmentPartition_related_eq consistent
  exact (input.quotientWire_eq_iff left right).1 equality

@[simp] theorem quotientWire_wireQuotient_origin (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    input.quotientWire (input.wireQuotient.origin quotient) = quotient := by
  apply input.wireQuotient.origin_injective
  simpa only [quotientWire, wireQuotient,
    VisualProof.Data.Finite.FinitePartition.quotientOrigin_classIndex] using
      (VisualProof.Data.Finite.FinitePartition.quotientDomain_survives_iff
        input.attachmentPartition _).1
          (input.wireQuotient.origin_survives quotient)

theorem equalBoundary_quotientWire_eq (input : Input )
    (left right : Fin input.pattern.val.boundary.length)
    (hequal : input.pattern.val.boundary.get left =
      input.pattern.val.boundary.get right) :
    input.quotientWire (input.attachment left) =
      input.quotientWire (input.attachment right) := by
  rw [input.quotientWire_eq_iff]
  exact FinitePartition.generator_related (edges := input.attachmentEdges)
    (edge := (input.attachment left, input.attachment right))
    ((input.mem_attachmentEdges_iff _).2 ⟨left, right, hequal, rfl⟩)

def AttachmentsVisible (input : Input ) : Prop :=
  ∀ position,
    input.frame.val.Encloses
      (input.frame.val.wires (input.attachment position)).scope input.site

def BinderTargetsInjective (input : Input ) : Prop :=
  Function.Injective input.binderTarget

def BinderTargetsMatch (input : Input ) : Prop :=
  ∀ index, ∃ parent,
    input.frame.val.regions (input.binderTarget index) =
      .bubble parent (input.binderSpine.arity index)

def BinderTargetsEnclose (input : Input ) : Prop :=
  ∀ index, input.frame.val.Encloses (input.binderTarget index) input.site

structure Admissible (input : Input ) : Prop where
  terminal_body : input.TerminalBody
  attachments_visible : input.AttachmentsVisible
  binder_targets_injective : input.BinderTargetsInjective
  binder_targets_match : input.BinderTargetsMatch
  binder_targets_enclose : input.BinderTargetsEnclose

instance (input : Input ) : Decidable input.AttachmentsVisible := by
  unfold AttachmentsVisible
  exact @Nat.decidableForallFin _ _ fun _ => inferInstance

instance (input : Input ) : Decidable input.BinderTargetsInjective := by
  unfold BinderTargetsInjective Function.Injective
  exact @Nat.decidableForallFin _ _ fun _ =>
    @Nat.decidableForallFin _ _ fun _ => inferInstance

instance (input : Input ) : Decidable input.BinderTargetsMatch := by
  unfold BinderTargetsMatch
  exact @Nat.decidableForallFin _ _ fun _ =>
    @Nat.decidableExistsFin _ _ fun _ => inferInstance

instance (input : Input ) : Decidable input.BinderTargetsEnclose := by
  unfold BinderTargetsEnclose
  exact @Nat.decidableForallFin _ _ fun _ => inferInstance

instance (input : Input ) : Decidable input.Admissible := by
  by_cases hterminal : input.TerminalBody
  · by_cases hvisible : input.AttachmentsVisible
    · by_cases hinjective : input.BinderTargetsInjective
      · by_cases hmatch : input.BinderTargetsMatch
        · by_cases henclose : input.BinderTargetsEnclose
          · exact isTrue {
              terminal_body := hterminal
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
  · exact isFalse fun hadmissible => hterminal hadmissible.terminal_body

inductive Error
  | nonterminalBinderSpine
  | attachmentNotVisible
  | duplicateBinderTarget
  | binderKindOrArityMismatch
  | binderDoesNotEncloseSite
  | resultNotWellFormed (error : WFError)
  deriving DecidableEq

abbrev CheckedInput :=
  { input : Input  // input.Admissible }

def checkInput (input : Input ) :
    Except Error (CheckedInput ) :=
  if hterminal : input.TerminalBody then
    if hvisible : input.AttachmentsVisible then
      if hinjective : input.BinderTargetsInjective then
        if hmatch : input.BinderTargetsMatch then
          if henclose : input.BinderTargetsEnclose then
            .ok ⟨input, {
              terminal_body := hterminal
              attachments_visible := hvisible
              binder_targets_injective := hinjective
              binder_targets_match := hmatch
              binder_targets_enclose := henclose
            }⟩
          else .error .binderDoesNotEncloseSite
        else .error .binderKindOrArityMismatch
      else .error .duplicateBinderTarget
    else .error .attachmentNotVisible
  else .error .nonterminalBinderSpine

theorem checkInput_sound
    (hcheck : checkInput input = .ok checked) :
    checked.val = input ∧ input.Admissible := by
  unfold checkInput at hcheck
  split at hcheck <;> try contradiction
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
  simp only [dif_pos hadmissible.terminal_body,
    dif_pos hadmissible.attachments_visible,
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

theorem related_eq_or_both_visible (input : Input )
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
def classWires (input : Input ) (quotient : input.wireQuotient.Carrier) :
    List (Fin input.frame.val.wireCount) :=
  filterFin fun wire => decide (input.quotientWire wire = quotient)

@[simp] theorem mem_classWires (input : Input )
    (quotient : input.wireQuotient.Carrier)
    (wire : Fin input.frame.val.wireCount) :
    wire ∈ input.classWires quotient ↔ input.quotientWire wire = quotient := by
  simp [classWires]

theorem classWires_nodup (input : Input )
    (quotient : input.wireQuotient.Carrier) :
  (input.classWires quotient).Nodup :=
  filterFin_nodup _

theorem classWires_quotientWire_eq_singleton (input : Input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    input.classWires (input.quotientWire wire) = [wire] := by
  have hmember : wire ∈ input.classWires (input.quotientWire wire) :=
    (input.mem_classWires _ wire).2 rfl
  have honly : ∀ candidate,
      candidate ∈ input.classWires (input.quotientWire wire) →
        candidate = wire := by
    intro candidate candidateMember
    exact input.quotientWire_injective consistent
      ((input.mem_classWires _ candidate).1 candidateMember)
  cases hclass : input.classWires (input.quotientWire wire) with
  | nil => simp [hclass] at hmember
  | cons head tail =>
      have hhead : head = wire := honly head (by simp [hclass])
      subst head
      have htail : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro candidate candidateMember
        have hcandidate := honly candidate (by simp [hclass, candidateMember])
        subst candidate
        have hnodup : (wire :: tail).Nodup := by
          rw [← hclass]
          exact input.classWires_nodup (input.quotientWire wire)
        exact (List.nodup_cons.mp hnodup).1 candidateMember
      subst tail
      rfl

theorem classWires_nonempty (input : Input )
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

def firstClassWire (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    Fin input.frame.val.wireCount :=
  (input.classWires quotient).get ⟨0, input.classWires_nonempty quotient⟩

@[simp] theorem quotientWire_firstClassWire (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    input.quotientWire (input.firstClassWire quotient) = quotient := by
  exact (input.mem_classWires quotient _).1 (List.get_mem _ _)

/-- Pick the outer member of a comparable pair, with stable left tie-break. -/
def chooseOuter (diagram : Diagram)
    (left right : Fin diagram.regionCount) : Fin diagram.regionCount :=
  if diagram.Encloses left right then left else right

def outermostFrom (diagram : Diagram) :
    Fin diagram.regionCount → List (Fin diagram.regionCount) →
      Fin diagram.regionCount
  | current, [] => current
  | current, next :: tail =>
      outermostFrom diagram (chooseOuter diagram current next) tail

theorem outermostFrom_encloses_of_common
    (diagram : Checked )
    (site current : Fin diagram.val.regionCount)
    (tail : List (Fin diagram.val.regionCount))
    (hcurrent : diagram.val.Encloses current site)
    (htail : ∀ region, region ∈ tail → diagram.val.Encloses region site) :
    diagram.val.Encloses (outermostFrom diagram.val current tail) current ∧
      ∀ region, region ∈ tail →
        diagram.val.Encloses (outermostFrom diagram.val current tail) region := by
  induction tail generalizing current with
  | nil => exact ⟨Diagram.Encloses.refl _ _, by simp⟩
  | cons next tail ih =>
      have hnext : diagram.val.Encloses next site := htail next (by simp)
      have hcomparable := diagram.val.enclosingRegions_comparable
        hcurrent hnext
      have hchosenCurrent :
          diagram.val.Encloses (chooseOuter diagram.val current next) current := by
        rcases hcomparable with hcurrentNext | hnextCurrent
        · simp [chooseOuter, hcurrentNext,
            Diagram.Encloses.refl]
        · by_cases hcurrentNext : diagram.val.Encloses current next
          · simp [chooseOuter, hcurrentNext,
              Diagram.Encloses.refl]
          · simpa [chooseOuter, hcurrentNext] using hnextCurrent
      have hchosenNext :
          diagram.val.Encloses (chooseOuter diagram.val current next) next := by
        by_cases hcurrentNext : diagram.val.Encloses current next
        · simp [chooseOuter, hcurrentNext]
        · simp [chooseOuter, hcurrentNext,
            Diagram.Encloses.refl]
      have hchosenSite :
          diagram.val.Encloses (chooseOuter diagram.val current next) site :=
        Elaboration.checked_encloses_trans diagram.property
          hchosenCurrent hcurrent
      have htailRest : ∀ region, region ∈ tail →
          diagram.val.Encloses region site := by
        intro region hregion
        exact htail region (by simp [hregion])
      have hresult := ih (chooseOuter diagram.val current next)
        hchosenSite htailRest
      constructor
      · exact Elaboration.checked_encloses_trans diagram.property
          hresult.1 hchosenCurrent
      · intro region hregion
        rw [List.mem_cons] at hregion
        rcases hregion with rfl | hregion
        · exact Elaboration.checked_encloses_trans diagram.property
            hresult.1 hchosenNext
        · exact hresult.2 region hregion

def classScopes (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    List (Fin input.frame.val.regionCount) :=
  (input.classWires quotient).map fun wire =>
    (input.frame.val.wires wire).scope

def classAllVisible (input : Input )
    (quotient : input.wireQuotient.Carrier) : Prop :=
  ∀ wire, wire ∈ input.classWires quotient →
    input.frame.val.Encloses (input.frame.val.wires wire).scope input.site

instance (input : Input ) (quotient : input.wireQuotient.Carrier) :
    Decidable (input.classAllVisible quotient) := by
  unfold classAllVisible
  infer_instance

/-- Deterministic outermost class-member scope; singleton nonattachments retain theirs. -/
def coalescedScope (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    Fin input.frame.val.regionCount :=
  let first := input.firstClassWire quotient
  if input.classAllVisible quotient then
    outermostFrom input.frame.val (input.frame.val.wires first).scope
      (input.classWires quotient |>.map fun wire =>
        (input.frame.val.wires wire).scope)
  else
    (input.frame.val.wires first).scope

@[simp] theorem coalescedScope_quotientWire (input : Input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    input.coalescedScope (input.quotientWire wire) =
      (input.frame.val.wires wire).scope := by
  have hclass := input.classWires_quotientWire_eq_singleton consistent wire
  unfold coalescedScope firstClassWire
  simp [hclass, outermostFrom, chooseOuter, Diagram.Encloses.refl]

private theorem outermostFrom_mem_cons (diagram : Diagram)
    (current : Fin diagram.regionCount)
    (tail : List (Fin diagram.regionCount)) :
    outermostFrom diagram current tail ∈ current :: tail := by
  induction tail generalizing current with
  | nil => simp [outermostFrom]
  | cons next tail ih =>
      simp only [outermostFrom]
      have hmember := ih (chooseOuter diagram current next)
      rw [List.mem_cons] at hmember
      rcases hmember with hchosen | htail
      · rw [hchosen]
        unfold chooseOuter
        split <;> simp
      · simp [htail]

/-- A coalesced scope is always the scope of a wire in its quotient class. -/
theorem coalescedScope_eq_member_scope (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    ∃ wire, wire ∈ input.classWires quotient ∧
      input.coalescedScope quotient = (input.frame.val.wires wire).scope := by
  by_cases hall : input.classAllVisible quotient
  · let first := input.firstClassWire quotient
    have hmember := outermostFrom_mem_cons input.frame.val
      (input.frame.val.wires first).scope (input.classScopes quotient)
    rw [List.mem_cons] at hmember
    rcases hmember with hfirst | hscope
    · refine ⟨first, ?_, ?_⟩
      · exact (input.mem_classWires quotient first).2
          (input.quotientWire_firstClassWire quotient)
      · simpa only [coalescedScope, hall, reduceIte, first] using hfirst
    · rw [classScopes, List.mem_map] at hscope
      obtain ⟨wire, hwire, hscope⟩ := hscope
      refine ⟨wire, hwire, ?_⟩
      simpa only [coalescedScope, hall, reduceIte, first] using hscope.symm
  · let first := input.firstClassWire quotient
    refine ⟨first, ?_, ?_⟩
    · exact (input.mem_classWires quotient first).2
        (input.quotientWire_firstClassWire quotient)
    · simp only [coalescedScope, hall, reduceIte, first]

theorem classWires_related (input : Input )
    (quotient : input.wireQuotient.Carrier)
    {left right : Fin input.frame.val.wireCount}
    (hleft : left ∈ input.classWires quotient)
    (hright : right ∈ input.classWires quotient) :
    input.attachmentPartition.related left right = true := by
  rw [← input.quotientWire_eq_iff]
  exact (input.mem_classWires quotient left).1 hleft |>.trans
    ((input.mem_classWires quotient right).1 hright).symm

theorem coalescedScope_encloses_member (input : Input )
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
      Diagram.Encloses.refl input.frame.val
        (input.frame.val.wires (input.firstClassWire quotient)).scope

/-- Exact endpoint union of an attachment class, in stable old-wire order. -/
def coalescedEndpoints (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    List (CEndpoint input.frame.val.nodeCount) :=
  (input.classWires quotient).flatMap fun wire =>
    (input.frame.val.wires wire).endpoints

@[simp] theorem coalescedEndpoints_quotientWire (input : Input)
    (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    input.coalescedEndpoints (input.quotientWire wire) =
      (input.frame.val.wires wire).endpoints := by
  simp [coalescedEndpoints,
    input.classWires_quotientWire_eq_singleton consistent wire]

def coalesceFrameRaw (input : Input ) : Diagram where
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

@[simp] theorem coalesceFrameRaw_regionCount (input : Input ) :
    input.coalesceFrameRaw.regionCount = input.frame.val.regionCount := rfl

@[simp] theorem coalesceFrameRaw_nodeCount (input : Input ) :
    input.coalesceFrameRaw.nodeCount = input.frame.val.nodeCount := rfl

@[simp] theorem coalesceFrameRaw_wireCount (input : Input ) :
    input.coalesceFrameRaw.wireCount = input.wireQuotient.count := rfl

@[simp] theorem coalesceFrameRaw_regions (input : Input )
    (region : Fin input.coalesceFrameRaw.regionCount) :
    input.coalesceFrameRaw.regions region = input.frame.val.regions region := rfl

@[simp] theorem coalesceFrameRaw_nodes (input : Input )
    (node : Fin input.coalesceFrameRaw.nodeCount) :
    input.coalesceFrameRaw.nodes node = input.frame.val.nodes node := rfl

@[simp] theorem coalesceFrameRaw_wire (input : Input )
    (wire : Fin input.coalesceFrameRaw.wireCount) :
    input.coalesceFrameRaw.wires wire = {
      scope := input.coalescedScope wire
      endpoints := input.coalescedEndpoints wire
    } := rfl

@[simp] theorem mem_coalescedEndpoints (input : Input )
    (quotient : input.wireQuotient.Carrier)
    (endpoint : CEndpoint input.frame.val.nodeCount) :
    endpoint ∈ input.coalescedEndpoints quotient ↔
      ∃ wire, wire ∈ input.classWires quotient ∧
        endpoint ∈ (input.frame.val.wires wire).endpoints := by
  simp [coalescedEndpoints]

theorem endpointLists_nodup
    (frame : Checked )
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
      simp [Diagram.EndpointOccurs, hendpoint] at hdisjoint

theorem checked_endpoint_wire_unique (diagram : Checked )
    (first second : Fin diagram.val.wireCount)
    (endpoint : CEndpoint diagram.val.nodeCount)
    (hfirst : diagram.val.EndpointOccurs first endpoint)
    (hsecond : diagram.val.EndpointOccurs second endpoint) :
    first = second := by
  by_cases heq : first = second
  · exact heq
  · have hdisjoint := diagram.property.wire_endpoints_are_disjoint
      first second (by simp [heq]) endpoint hfirst
    have hoccurs : decide (diagram.val.EndpointOccurs second endpoint) = true :=
      decide_eq_true_iff.mpr hsecond
    rw [hoccurs] at hdisjoint
    contradiction

theorem coalescedEndpoints_nodup (input : Input )
    (quotient : input.wireQuotient.Carrier) :
    (input.coalescedEndpoints quotient).Nodup :=
  endpointLists_nodup input.frame (input.classWires quotient)
    (input.classWires_nodup quotient)

theorem coalesceFrameRaw_climb (input : Input )
    (steps : Nat) (region : Fin input.frame.val.regionCount) :
    input.coalesceFrameRaw.climb steps region =
      input.frame.val.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      cases hparent : (input.frame.val.regions region).parent? with
      | none =>
          simp [Diagram.climb, coalesceFrameRaw_regions, hparent]
      | some parent =>
          simp [Diagram.climb, coalesceFrameRaw_regions,
            hparent, ih parent]

theorem coalesceFrameRaw_encloses_iff (input : Input )
    (ancestor descendant : Fin input.frame.val.regionCount) :
    input.coalesceFrameRaw.Encloses ancestor descendant ↔
      input.frame.val.Encloses ancestor descendant := by
  unfold Diagram.Encloses
  constructor <;> rintro ⟨steps, hsteps⟩ <;> refine ⟨steps, ?_⟩
  · rw [input.coalesceFrameRaw_climb] at hsteps
    exact hsteps
  · rw [input.coalesceFrameRaw_climb]
    exact hsteps

theorem endpointOccurs_quotient (input : Input )
    (wire : Fin input.frame.val.wireCount)
    (endpoint : CEndpoint input.frame.val.nodeCount)
    (hoccurs : input.frame.val.EndpointOccurs wire endpoint) :
    input.coalesceFrameRaw.EndpointOccurs (input.quotientWire wire) endpoint := by
  change endpoint ∈ input.coalescedEndpoints (input.quotientWire wire)
  rw [input.mem_coalescedEndpoints]
  exact ⟨wire, (input.mem_classWires _ wire).2 rfl, hoccurs⟩

theorem coalesceFrameRaw_wellFormed (input : Input )
    (hadmissible : input.Admissible) :
    input.coalesceFrameRaw.WellFormed  where
  root_is_sheet := input.frame.property.root_is_sheet
  only_root_is_sheet := input.frame.property.only_root_is_sheet
  all_regions_reach_root := by
    intro region
    unfold Diagram.ReachesRoot
    rw [input.coalesceFrameRaw_encloses_iff]
    exact input.frame.property.all_regions_reach_root region
  atom_binders_are_bubbles := by
    unfold Diagram.AtomBindersAreBubbles
    intro node
    change Fin input.frame.val.nodeCount at node
    have hold := input.frame.property.atom_binders_are_bubbles node
    cases hnode : input.frame.val.nodes node with
    | identity => simp [coalesceFrameRaw_nodes, hnode]
    | atom region binder =>
        simp only [hnode] at hold
        simpa [coalesceFrameRaw_nodes, coalesceFrameRaw_regions, hnode] using hold
  atom_binders_enclose := by
    intro node
    change Fin input.frame.val.nodeCount at node
    simp only [coalesceFrameRaw_nodes]
    cases hnode : input.frame.val.nodes node with
    | identity => trivial
    | atom region binder =>
        simp only
        rw [input.coalesceFrameRaw_encloses_iff]
        simpa only [hnode] using input.frame.property.atom_binders_enclose node
  endpoints_are_valid := by
    intro quotient endpoint hendpoint
    change input.wireQuotient.Carrier at quotient
    change CEndpoint input.frame.val.nodeCount at endpoint
    change endpoint ∈ input.coalescedEndpoints quotient at hendpoint
    rw [input.mem_coalescedEndpoints] at hendpoint
    rcases hendpoint with ⟨wire, _, hwire⟩
    have hvalid := input.frame.property.endpoints_are_valid
      wire endpoint hwire
    unfold Diagram.RequiresPort at hvalid ⊢
    cases hnode : input.frame.val.nodes endpoint.node with
    | identity =>
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
            simp [Diagram.EndpointOccurs, hsecondEndpoint] at hdisjoint))
      _ = true := rfl
  required_ports_are_covered := by
    unfold Diagram.RequiredPortsAreCovered
    intro node
    have hcovered := input.frame.property.required_ports_are_covered node
    simp only [coalesceFrameRaw_nodes, coalesceFrameRaw_regions]
    cases hnode : input.frame.val.nodes node with
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
    | identity region arity =>
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
    exact Elaboration.checked_encloses_trans input.frame.property hscope hold

/-- Stable material/proxy and internal-wire blocks for plugging. -/
structure PlugLayout (input : Input ) where
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

end Input

end VisualProof.Concrete.Splice
