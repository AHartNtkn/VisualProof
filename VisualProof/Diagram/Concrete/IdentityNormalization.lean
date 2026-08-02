import VisualProof.Diagram.Concrete.IdentityNormalizationTransport
import VisualProof.Diagram.Concrete.IdentityNormalizationDropWellFormed
import VisualProof.Diagram.Concrete.IdentityNormalizationCollapseWellFormed
import VisualProof.Diagram.Concrete.IdentityNormalizationFusionWellFormed

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

/-- The construction-owned primitive and complete eligibility receipt for one
eager identity rewrite.  Consumers never need to rediscover which rule made a
target or re-run eligibility search. -/
inductive IdentityRewriteKind
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type
  | drop
      (node : source.val.NodeId)
      (eligible : DropEligibility source node)
  | collapse
      (node : source.val.NodeId)
      (eligible : CollapseEligibility source node)
  | fusion
      (left right : source.val.NodeId)
      (eligible : FusionEligibility source left right)

namespace IdentityRewriteKind

/-- Source nodes deleted by the rewrite, in construction order. -/
def removedNodes : IdentityRewriteKind source → List source.val.NodeId
  | .drop node _ => [node]
  | .collapse node _ => [node]
  | .fusion _ right _ => [right]

/-- Source nodes retained by the rewrite, in canonical dense order. -/
def retainedNodes (kind : IdentityRewriteKind source) :
    List source.val.NodeId :=
  IdentityNormalizationCore.retainedNodes source.val kind.removedNodes

/-- Original storage-port owners, in port-index order, for every identity
represented by this rewrite.  Fusion deliberately retains two separate
attachment lists rather than only their distinct-wire union. -/
def sourceIdentityAttachments :
    IdentityRewriteKind source → List (List source.val.WireId)
  | .drop node eligible =>
      [source.val.identityOwners node eligible.identity.arity]
  | .collapse node eligible =>
      [source.val.identityOwners node eligible.identity.arity]
  | .fusion left right eligible =>
      [ source.val.identityOwners left eligible.leftIdentity.arity
      , source.val.identityOwners right eligible.rightIdentity.arity ]

end IdentityRewriteKind

/-- One checked eager rewrite with total signature-preserving wire transport. -/
structure IdentityRewrite
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type where
  kind : IdentityRewriteKind source
  target : CheckedDiagram definitions
  target_generated :
    match kind with
    | .drop node eligible =>
        target.val = dropCandidate source node eligible
    | .collapse node eligible =>
        target.val = collapseCandidate source node eligible
    | .fusion left right eligible =>
        target.val = fusionCandidate source left right eligible
  wireImage : source.val.WireId → target.val.WireId
  wire_signature :
    ∀ wire,
      (target.val.wires (wireImage wire)).sig =
        (source.val.wires wire).sig
  nodeCount_lt : target.val.nodeCount < source.val.nodeCount

namespace IdentityRewrite

/-- Every normalization rewrite preserves regions and their dense ids. -/
def regionImage
    (rewrite : IdentityRewrite source)
    (region : source.val.RegionId) : rewrite.target.val.RegionId := by
  refine ⟨region.val, ?_⟩
  cases kindEquation : rewrite.kind with
  | drop node eligible =>
      have generated := rewrite.target_generated
      rw [kindEquation] at generated
      rw [generated]
      simpa [dropCandidate, eraseNodeCandidate] using region.isLt
  | collapse node eligible =>
      have generated := rewrite.target_generated
      rw [kindEquation] at generated
      rw [generated]
      simpa [collapseCandidate] using region.isLt
  | fusion left right eligible =>
      have generated := rewrite.target_generated
      rw [kindEquation] at generated
      rw [generated]
      simpa [fusionCandidate] using region.isLt

/-- Exact dense image of a retained source node. -/
def nodeImage?
    (rewrite : IdentityRewrite source)
    (node : source.val.NodeId) : Option rewrite.target.val.NodeId := by
  let retained := rewrite.kind.retainedNodes
  match found : Data.Finite.indexOf? retained node with
  | none => exact none
  | some position =>
      exact some ⟨position.val, by
        have positionBound := position.isLt
        cases kindEquation : rewrite.kind with
        | drop removed eligible =>
            have generated := rewrite.target_generated
            rw [kindEquation] at generated
            rw [generated]
            have retainedExact :
                retained =
                  IdentityNormalizationCore.retainedNodes source.val
                    [removed] := by
              simp [retained, IdentityRewriteKind.retainedNodes,
                kindEquation, IdentityRewriteKind.removedNodes]
            have countExact :
                retained.length =
                  (dropCandidate source removed eligible).nodeCount := by
              rw [retainedExact]
              rfl
            omega
        | collapse removed eligible =>
            have generated := rewrite.target_generated
            rw [kindEquation] at generated
            rw [generated]
            have retainedExact :
                retained =
                  IdentityNormalizationCore.retainedNodes source.val
                    [removed] := by
              simp [retained, IdentityRewriteKind.retainedNodes,
                kindEquation, IdentityRewriteKind.removedNodes]
            have countExact :
                retained.length =
                  (collapseCandidate source removed eligible).nodeCount := by
              rw [retainedExact]
              rfl
            omega
        | fusion left right eligible =>
            have generated := rewrite.target_generated
            rw [kindEquation] at generated
            rw [generated]
            have retainedExact :
                retained =
                  IdentityNormalizationCore.retainedNodes source.val
                    [right] := by
              simp [retained, IdentityRewriteKind.retainedNodes,
                kindEquation, IdentityRewriteKind.removedNodes]
            have countExact :
                retained.length =
                  (fusionCandidate source left right eligible).nodeCount := by
              rw [retainedExact]
              rfl
            omega⟩

end IdentityRewrite

private def dropRewrite
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    IdentityRewrite source :=
  let candidate := dropCandidate source node eligible
  let target : CheckedDiagram definitions :=
    ⟨candidate, dropCandidate_wellFormed source node eligible⟩
  let transport := dropWireTransport source node eligible
  { kind := .drop node eligible
    target := target
    target_generated := rfl
    wireImage := transport.wireImage
    wire_signature := transport.wire_signature
    nodeCount_lt := dropCandidate_nodeCount_lt source node eligible }

/-- Rule 1: delete a physically one-wire identity as reflexive truth. -/
def dropDegenerate
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Option (IdentityRewrite source) :=
  (dropEligibility? source node).map (dropRewrite source node)

private def collapseRewrite
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    IdentityRewrite source :=
  let candidate := collapseCandidate source node eligible
  let target : CheckedDiagram definitions :=
    ⟨candidate, collapseCandidate_wellFormed source node eligible⟩
  let transport := collapseWireTransport source node eligible
  { kind := .collapse node eligible
    target := target
    target_generated := rfl
    wireImage := transport.wireImage
    wire_signature := transport.wire_signature
    nodeCount_lt := collapseCandidate_nodeCount_lt source node eligible }

/--
Rule 2: collapse one identity whose incident wires have at most one outer
scope.  The unique outer wire survives when present.
-/
def collapseOnePoint
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    Option (IdentityRewrite source) :=
  (collapseEligibility? source node).map
    (collapseRewrite source node)

private def fusionRewrite
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    IdentityRewrite source :=
  let candidate := fusionCandidate source left right eligible
  let target : CheckedDiagram definitions :=
    ⟨candidate, fusionCandidate_wellFormed source left right eligible⟩
  let transport := fusionWireTransport source left right eligible
  { kind := .fusion left right eligible
    target := target
    target_generated := rfl
    wireImage := transport.wireImage
    wire_signature := transport.wire_signature
    nodeCount_lt :=
      fusionCandidate_nodeCount_lt source left right eligible }

/-- Rule 3: fuse two same-region identities by unordered distinct-wire union. -/
def fuseSameRegion
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    Option (IdentityRewrite source) :=
  (fusionEligibility? source left right).map
    (fusionRewrite source left right)

/-- Chronological construction trace retained by eager normalization. -/
inductive IdentityNormalizationTrace
    (definitions : List (List Sig)) :
    (source : CheckedDiagram definitions) → Type
  | done (source) : IdentityNormalizationTrace definitions source
  | step (first : IdentityRewrite source)
      (rest : IdentityNormalizationTrace definitions first.target) :
      IdentityNormalizationTrace definitions source

namespace IdentityNormalizationTrace

def target : IdentityNormalizationTrace definitions source →
    CheckedDiagram definitions
  | .done source => source
  | .step _ rest => rest.target

def wireImage :
    (trace : IdentityNormalizationTrace definitions source) →
      source.val.WireId → trace.target.val.WireId
  | .done _, wire => wire
  | .step first rest, wire => rest.wireImage (first.wireImage wire)

theorem wire_signature
    (trace : IdentityNormalizationTrace definitions source)
    (wire : source.val.WireId) :
    (trace.target.val.wires (trace.wireImage wire)).sig =
      (source.val.wires wire).sig := by
  induction trace with
  | done => rfl
  | step first rest induction =>
      exact (induction (first.wireImage wire)).trans
        (first.wire_signature wire)

end IdentityNormalizationTrace

/-- The checked fixpoint with its chronological construction trace. -/
structure IdentityNormalization
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type where
  private mk ::
  trace : IdentityNormalizationTrace definitions source

namespace IdentityNormalization

def target
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (normalization : IdentityNormalization source) :
    CheckedDiagram definitions :=
  normalization.trace.target

def wireImage
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (normalization : IdentityNormalization source) :
    source.val.WireId → normalization.target.val.WireId :=
  normalization.trace.wireImage

theorem wire_signature
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    (normalization : IdentityNormalization source)
    (wire : source.val.WireId) :
    (normalization.target.val.wires
      (normalization.wireImage wire)).sig =
      (source.val.wires wire).sig :=
  normalization.trace.wire_signature wire

end IdentityNormalization

private def firstDrop?
    (source : CheckedDiagram definitions) :
    Option (IdentityRewrite source) :=
  (identityNodeIds source.val).findSome? fun node =>
    dropDegenerate source node

private def firstCollapse?
    (source : CheckedDiagram definitions) :
    Option (IdentityRewrite source) :=
  (identityNodeIds source.val).findSome? fun node =>
    collapseOnePoint source node

private def fusionSearch?
    (source : CheckedDiagram definitions) :
    List source.val.NodeId → Option (IdentityRewrite source)
  | [] => none
  | left :: tail =>
      match tail.findSome? fun right =>
        fuseSameRegion source left right with
      | some result => some result
      | none => fusionSearch? source tail

private def firstFusion?
    (source : CheckedDiagram definitions) :
    Option (IdentityRewrite source) :=
  fusionSearch? source (identityNodeIds source.val)

/-- No propositional Rule-1 receipt exists at any node. -/
def DropExhausted (source : CheckedDiagram definitions) : Prop :=
  ∀ node, ¬ Nonempty (DropEligibility source node)

/-- No propositional Rule-2 receipt exists at any node. -/
def CollapseExhausted (source : CheckedDiagram definitions) : Prop :=
  ∀ node, ¬ Nonempty (CollapseEligibility source node)

/-- No propositional Rule-3 receipt exists at any ordered node pair. -/
def FusionExhausted (source : CheckedDiagram definitions) : Prop :=
  ∀ left right, ¬ Nonempty (FusionEligibility source left right)

/-- The public receipt-level characterization of executable normality. -/
def IdentityRewriteExhausted (source : CheckedDiagram definitions) : Prop :=
  DropExhausted source ∧ CollapseExhausted source ∧ FusionExhausted source

/-- Apply exactly the first eligible rewrite in Rule 1→2→3 priority. -/
def normalizeOneIdentity
    (source : CheckedDiagram definitions) :
    Option (IdentityRewrite source) :=
  match firstDrop? source with
  | some result => some result
  | none =>
      match firstCollapse? source with
      | some result => some result
      | none => firstFusion? source

/-- Evidence that a retained trace follows the executable normalization
priority exactly, rather than merely chaining arbitrary rewrites. -/
inductive IdentityNormalizationTrace.Valid :
    {source : CheckedDiagram definitions} →
      IdentityNormalizationTrace definitions source → Prop
  | done
      (exhausted : normalizeOneIdentity source = none) :
      Valid (.done source)
  | step
      (selected : normalizeOneIdentity source = some first)
      (restValid : Valid rest) :
      Valid (.step first rest)

private theorem findSome?_provenance
    {items : List α}
    {select : α → Option β}
    {result : β}
    (found : items.findSome? select = some result) :
    ∃ item, item ∈ items ∧ select item = some result :=
  List.exists_of_findSome?_eq_some found

private theorem fusionSearch?_provenance
    (source : CheckedDiagram definitions) :
    ∀ candidates result,
      fusionSearch? source candidates = some result →
      ∃ left, left ∈ candidates ∧
        ∃ right, right ∈ candidates ∧
          fuseSameRegion source left right = some result := by
  intro candidates
  induction candidates with
  | nil =>
      intro result found
      simp [fusionSearch?] at found
  | cons left tail induction =>
      intro result found
      unfold fusionSearch? at found
      cases pairEquation :
          tail.findSome? fun right =>
            fuseSameRegion source left right with
      | some pairResult =>
          rw [pairEquation] at found
          have resultEquation : pairResult = result :=
            Option.some.inj found
          subst pairResult
          obtain ⟨right, rightMember, rightFound⟩ :=
            findSome?_provenance pairEquation
          exact ⟨left, by simp, right,
            List.mem_cons_of_mem left rightMember, rightFound⟩
      | none =>
          rw [pairEquation] at found
          obtain ⟨foundLeft, leftMember, foundRight, rightMember,
              ruleFound⟩ :=
            induction result found
          exact ⟨foundLeft, List.mem_cons_of_mem left leftMember,
            foundRight, List.mem_cons_of_mem left rightMember, ruleFound⟩

private theorem firstDrop?_none_iff
    (source : CheckedDiagram definitions) :
    firstDrop? source = none ↔ DropExhausted source := by
  unfold firstDrop? DropExhausted
  constructor
  · intro exhausted node ⟨eligible⟩
    have nodeMember := eligible.identity.mem_identityNodeIds
    have nodeNone :=
      List.findSome?_eq_none_iff.mp exhausted node nodeMember
    obtain ⟨found, foundEq⟩ :=
      dropEligibility?_complete source node eligible
    unfold dropDegenerate at nodeNone
    rw [foundEq] at nodeNone
    contradiction
  · intro exhausted
    apply List.findSome?_eq_none_iff.mpr
    intro node _
    unfold dropDegenerate
    cases found : dropEligibility? source node with
    | none => rfl
    | some eligible => exact False.elim (exhausted node ⟨eligible⟩)

private theorem firstCollapse?_none_iff
    (source : CheckedDiagram definitions) :
    firstCollapse? source = none ↔ CollapseExhausted source := by
  unfold firstCollapse? CollapseExhausted
  constructor
  · intro exhausted node ⟨eligible⟩
    have nodeMember := eligible.identity.mem_identityNodeIds
    have nodeNone :=
      List.findSome?_eq_none_iff.mp exhausted node nodeMember
    obtain ⟨found, foundEq⟩ :=
      collapseEligibility?_complete source node eligible
    unfold collapseOnePoint at nodeNone
    rw [foundEq] at nodeNone
    contradiction
  · intro exhausted
    apply List.findSome?_eq_none_iff.mpr
    intro node _
    unfold collapseOnePoint
    cases found : collapseEligibility? source node with
    | none => rfl
    | some eligible => exact False.elim (exhausted node ⟨eligible⟩)

private theorem fusionSearch?_some_of_eligible
    (source : CheckedDiagram definitions)
    (candidates : List source.val.NodeId)
    (left right : source.val.NodeId)
    (leftMember : left ∈ candidates)
    (rightMember : right ∈ candidates)
    (eligible : FusionEligibility source left right) :
    ∃ result, fusionSearch? source candidates = some result := by
  induction candidates with
  | nil => simp at leftMember
  | cons head tail induction =>
      by_cases headLeft : head = left
      · subst head
        have rightTail : right ∈ tail := by
          rcases List.mem_cons.mp rightMember with same | member
          · exact False.elim (eligible.distinct same.symm)
          · exact member
        obtain ⟨foundEligible, eligibilityEq⟩ :=
          fusionEligibility?_complete source left right eligible
        have rewriteExists :
            ∃ rewrite, fuseSameRegion source left right = some rewrite := by
          exact ⟨fusionRewrite source left right foundEligible, by
            simp [fuseSameRegion, eligibilityEq]⟩
        unfold fusionSearch?
        cases pairEq : tail.findSome? fun candidate =>
            fuseSameRegion source left candidate with
        | some result => exact ⟨result, rfl⟩
        | none =>
            obtain ⟨rewrite, rewriteEq⟩ := rewriteExists
            have impossible :=
              List.findSome?_eq_none_iff.mp pairEq right rightTail
            rw [rewriteEq] at impossible
            contradiction
      · by_cases headRight : head = right
        · subst head
          have leftTail : left ∈ tail := by
            rcases List.mem_cons.mp leftMember with same | member
            · exact False.elim (eligible.distinct same)
            · exact member
          let symmetric := eligible.symm
          obtain ⟨foundEligible, eligibilityEq⟩ :=
            fusionEligibility?_complete source right left symmetric
          have rewriteExists :
              ∃ rewrite, fuseSameRegion source right left = some rewrite := by
            exact ⟨fusionRewrite source right left foundEligible, by
              simp [fuseSameRegion, eligibilityEq]⟩
          unfold fusionSearch?
          cases pairEq : tail.findSome? fun candidate =>
              fuseSameRegion source right candidate with
          | some result => exact ⟨result, rfl⟩
          | none =>
              obtain ⟨rewrite, rewriteEq⟩ := rewriteExists
              have impossible :=
                List.findSome?_eq_none_iff.mp pairEq left leftTail
              rw [rewriteEq] at impossible
              contradiction
        · have leftTail : left ∈ tail :=
            (List.mem_cons.mp leftMember).resolve_left
              (fun same => headLeft same.symm)
          have rightTail : right ∈ tail :=
            (List.mem_cons.mp rightMember).resolve_left
              (fun same => headRight same.symm)
          obtain ⟨recursive, recursiveEq⟩ :=
            induction leftTail rightTail
          unfold fusionSearch?
          cases pairEq : tail.findSome? fun candidate =>
              fuseSameRegion source head candidate with
          | some result => exact ⟨result, rfl⟩
          | none => exact ⟨recursive, recursiveEq⟩

private theorem firstFusion?_none_iff
    (source : CheckedDiagram definitions) :
    firstFusion? source = none ↔ FusionExhausted source := by
  constructor
  · intro exhausted left right ⟨eligible⟩
    have leftMember := eligible.leftIdentity.mem_identityNodeIds
    have rightMember := eligible.rightIdentity.mem_identityNodeIds
    obtain ⟨result, found⟩ := fusionSearch?_some_of_eligible source
      (identityNodeIds source.val) left right leftMember rightMember eligible
    unfold firstFusion? at exhausted
    rw [found] at exhausted
    contradiction
  · intro exhausted
    unfold firstFusion?
    cases found : fusionSearch? source (identityNodeIds source.val) with
    | none => rfl
    | some result =>
        obtain ⟨left, _, right, _, ruleFound⟩ :=
          fusionSearch?_provenance source
            (identityNodeIds source.val) result found
        unfold fuseSameRegion at ruleFound
        cases eligibilityEq : fusionEligibility? source left right with
        | none => simp [eligibilityEq] at ruleFound
        | some eligible => exact False.elim (exhausted left right ⟨eligible⟩)

/-- The executable one-step normalizer reports exhaustion exactly when no
receipt for any of its three primitive classes exists. -/
theorem normalizeOneIdentity_eq_none_iff
    (source : CheckedDiagram definitions) :
    normalizeOneIdentity source = none ↔ IdentityRewriteExhausted source := by
  constructor
  · intro normalized
    unfold normalizeOneIdentity at normalized
    cases dropEq : firstDrop? source with
    | some result => simp [dropEq] at normalized
    | none =>
        have noDrop := (firstDrop?_none_iff source).mp dropEq
        rw [dropEq] at normalized
        cases collapseEq : firstCollapse? source with
        | some result => simp [collapseEq] at normalized
        | none =>
            have noCollapse :=
              (firstCollapse?_none_iff source).mp collapseEq
            rw [collapseEq] at normalized
            have noFusion := (firstFusion?_none_iff source).mp normalized
            exact ⟨noDrop, noCollapse, noFusion⟩
  · rintro ⟨noDrop, noCollapse, noFusion⟩
    unfold normalizeOneIdentity
    rw [(firstDrop?_none_iff source).mpr noDrop,
      (firstCollapse?_none_iff source).mpr noCollapse,
      (firstFusion?_none_iff source).mpr noFusion]

/--
Every successful eager step is exactly one public primitive rule result.
Private search order remains owned by `normalizeOneIdentity`.
-/
theorem normalizeOne_provenance
    (source : CheckedDiagram definitions)
    (result : IdentityRewrite source)
    (found : normalizeOneIdentity source = some result) :
    (∃ node, node ∈ identityNodeIds source.val ∧
      dropDegenerate source node = some result) ∨
    (∃ node, node ∈ identityNodeIds source.val ∧
      collapseOnePoint source node = some result) ∨
    (∃ left, left ∈ identityNodeIds source.val ∧
      ∃ right, right ∈ identityNodeIds source.val ∧
        fuseSameRegion source left right = some result) := by
  unfold normalizeOneIdentity at found
  cases dropEquation : firstDrop? source with
  | some dropResult =>
      rw [dropEquation] at found
      have resultEquation : dropResult = result :=
        Option.some.inj found
      subst dropResult
      left
      unfold firstDrop? at dropEquation
      exact findSome?_provenance dropEquation
  | none =>
      rw [dropEquation] at found
      cases collapseEquation : firstCollapse? source with
      | some collapseResult =>
          rw [collapseEquation] at found
          have resultEquation : collapseResult = result :=
            Option.some.inj found
          subst collapseResult
          right
          left
          unfold firstCollapse? at collapseEquation
          exact findSome?_provenance collapseEquation
      | none =>
          rw [collapseEquation] at found
          right
          right
          unfold firstFusion? at found
          exact fusionSearch?_provenance source
            (identityNodeIds source.val) result found

/-- Priority-aware public classification of a successful executable step.
Unlike raw provenance, later constructors retain proof that every higher
rewrite class was exhausted. -/
inductive NormalizeOneSelection
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (result : IdentityRewrite source) : Prop
  | drop
      (node : source.val.NodeId)
      (eligible : DropEligibility source node)
      (kind_eq : result.kind = .drop node eligible)
  | collapse
      (noDrop : DropExhausted source)
      (node : source.val.NodeId)
      (eligible : CollapseEligibility source node)
      (kind_eq : result.kind = .collapse node eligible)
  | fusion
      (noDrop : DropExhausted source)
      (noCollapse : CollapseExhausted source)
      (left right : source.val.NodeId)
      (eligible : FusionEligibility source left right)
      (kind_eq : result.kind = .fusion left right eligible)

private theorem dropDegenerate_kind
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (result : IdentityRewrite source)
    (found : dropDegenerate source node = some result) :
    ∃ eligible, result.kind = .drop node eligible := by
  unfold dropDegenerate at found
  cases eligibilityEq : dropEligibility? source node with
  | none => simp [eligibilityEq] at found
  | some eligible =>
      simp [eligibilityEq] at found
      subst result
      exact ⟨eligible, rfl⟩

private theorem collapseOnePoint_kind
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (result : IdentityRewrite source)
    (found : collapseOnePoint source node = some result) :
    ∃ eligible, result.kind = .collapse node eligible := by
  unfold collapseOnePoint at found
  cases eligibilityEq : collapseEligibility? source node with
  | none => simp [eligibilityEq] at found
  | some eligible =>
      simp [eligibilityEq] at found
      subst result
      exact ⟨eligible, rfl⟩

private theorem fuseSameRegion_kind
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (result : IdentityRewrite source)
    (found : fuseSameRegion source left right = some result) :
    ∃ eligible, result.kind = .fusion left right eligible := by
  unfold fuseSameRegion at found
  cases eligibilityEq : fusionEligibility? source left right with
  | none => simp [eligibilityEq] at found
  | some eligible =>
      simp [eligibilityEq] at found
      subst result
      exact ⟨eligible, rfl⟩

/-- Every successful deterministic step carries exactly the public primitive
receipt selected by Rule 1→2→3 priority. -/
theorem normalizeOne_selection
    (source : CheckedDiagram definitions)
    (result : IdentityRewrite source)
    (found : normalizeOneIdentity source = some result) :
    NormalizeOneSelection source result := by
  unfold normalizeOneIdentity at found
  cases dropEq : firstDrop? source with
  | some dropResult =>
      rw [dropEq] at found
      have exactResult := Option.some.inj found
      subst dropResult
      obtain ⟨node, _, ruleFound⟩ :=
        findSome?_provenance dropEq
      obtain ⟨eligible, kindEq⟩ :=
        dropDegenerate_kind source node result ruleFound
      exact .drop node eligible kindEq
  | none =>
      rw [dropEq] at found
      have noDrop := (firstDrop?_none_iff source).mp dropEq
      cases collapseEq : firstCollapse? source with
      | some collapseResult =>
          rw [collapseEq] at found
          have exactResult := Option.some.inj found
          subst collapseResult
          obtain ⟨node, _, ruleFound⟩ :=
            findSome?_provenance collapseEq
          obtain ⟨eligible, kindEq⟩ :=
            collapseOnePoint_kind source node result ruleFound
          exact .collapse noDrop node eligible kindEq
      | none =>
          rw [collapseEq] at found
          have noCollapse :=
            (firstCollapse?_none_iff source).mp collapseEq
          unfold firstFusion? at found
          obtain ⟨left, _, right, _, ruleFound⟩ :=
            fusionSearch?_provenance source
              (identityNodeIds source.val) result found
          obtain ⟨eligible, kindEq⟩ :=
            fuseSameRegion_kind source left right result ruleFound
          exact .fusion noDrop noCollapse left right eligible kindEq

/-- Every nonempty valid trace exposes the exact public rewrite constructor
that produced its first checked target. -/
theorem IdentityNormalizationTrace.Valid.first_provenance
    {source : CheckedDiagram definitions}
    {first : IdentityRewrite source}
    {rest : IdentityNormalizationTrace definitions first.target}
    (valid : IdentityNormalizationTrace.Valid (.step first rest)) :
    (∃ node, node ∈ identityNodeIds source.val ∧
      dropDegenerate source node = some first) ∨
    (∃ node, node ∈ identityNodeIds source.val ∧
      collapseOnePoint source node = some first) ∨
    (∃ left, left ∈ identityNodeIds source.val ∧
      ∃ right, right ∈ identityNodeIds source.val ∧
        fuseSameRegion source left right = some first) := by
  cases valid with
  | step selected _ =>
      exact normalizeOne_provenance source first selected

private def identityNormalizationRefl
    (source : CheckedDiagram definitions) :
    IdentityNormalization source :=
  ⟨.done source⟩

private def composeNormalization
    (first : IdentityRewrite source)
    (rest : IdentityNormalization first.target) :
    IdentityNormalization source :=
  ⟨.step first rest.trace⟩

/--
Deterministic eager Rule 1→2→3 fixpoint. Recursion is justified directly by
the node removed by each checked rewrite; there is no fuel fallback.
-/
def normalizeIdentities
    (source : CheckedDiagram definitions) :
    IdentityNormalization source :=
  match normalizeOneIdentity source with
  | none => identityNormalizationRefl source
  | some first =>
      composeNormalization first (normalizeIdentities first.target)
termination_by source.val.nodeCount
decreasing_by
  exact first.nodeCount_lt

/-- The retained chronological trace is exactly the deterministic eager run. -/
theorem normalizeIdentities_trace_valid
    (source : CheckedDiagram definitions) :
    (normalizeIdentities source).trace.Valid := by
  rw [normalizeIdentities]
  cases selected : normalizeOneIdentity source with
  | none => exact .done selected
  | some first =>
      exact .step selected (normalizeIdentities_trace_valid first.target)
termination_by source.val.nodeCount
decreasing_by
  exact first.nodeCount_lt

end ConcreteDiagram

end VisualProof
