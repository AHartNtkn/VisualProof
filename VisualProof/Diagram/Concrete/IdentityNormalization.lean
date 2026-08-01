import VisualProof.Diagram.Concrete.IdentityNormalizationTransport
import VisualProof.Diagram.Concrete.IdentityNormalizationDropWellFormed
import VisualProof.Diagram.Concrete.IdentityNormalizationCollapseWellFormed
import VisualProof.Diagram.Concrete.IdentityNormalizationFusionWellFormed

namespace VisualProof

namespace ConcreteDiagram

open IdentityNormalizationCore

/-- One checked eager rewrite with total signature-preserving wire transport. -/
structure IdentityRewrite
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions) : Type where
  target : CheckedDiagram definitions
  wireImage : source.val.WireId → target.val.WireId
  wire_signature :
    ∀ wire,
      (target.val.wires (wireImage wire)).sig =
        (source.val.wires wire).sig
  nodeCount_lt : target.val.nodeCount < source.val.nodeCount

private def dropRewrite
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    IdentityRewrite source :=
  let candidate := dropCandidate source node eligible
  let target : CheckedDiagram definitions :=
    ⟨candidate, dropCandidate_wellFormed source node eligible⟩
  let transport := dropWireTransport source node eligible
  { target := target
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
  { target := target
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
  { target := target
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
