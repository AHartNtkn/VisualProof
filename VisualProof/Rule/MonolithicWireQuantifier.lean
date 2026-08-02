import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.WireQuantifierRelationSever
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoin
import VisualProof.Diagram.Concrete.WireQuantifierRelationSeverInsertionSemantics
import VisualProof.Rule.Structural
import VisualProof.Rule.WirePrimitive.Site

namespace VisualProof

universe u

namespace MonolithicWireQuantifier

/-- Stable refusal outcomes of the strongest wire-quantifier checker. -/
inductive MonolithicWireQuantifierError
  | expectedRelation
  | severRequiresPositive
  | severBackwardRequiresNegative
  | joinRequiresNegative
  | joinBackwardRequiresPositive
  | emptyOccurrenceList
  | extractionRejected (error : ExtractionError)
  | occurrenceOutsideScope
  | occurrencesOverlap
  | formalNotOnBoundary
  | formalSignatureMismatch
  | contentMismatch
  | parameterMismatch
  | parameterOutsideScope
  | dyingWireIsParameter
  | boundaryTooShort
  | boundarySignatureMismatch
  | nonAppliedEndpoint
  | repeatedApplication
  | applicationSignatureMismatch
  | missingApplicationArgument
  | applicationOutsideScope
  | contentCompilationFailed
  | concreteRejected (error : ConcreteWireQuantifier.Error)
  | parameterTransportFailed
  | inverseRelationJoinRejected
  | inverseReconstructionRejected
  deriving Repr, DecidableEq

/--
One explicitly designated exact occurrence.

The occurrence owns its extent and canonical boundary. `formals` is separate,
ordered user input; repetitions are meaningful relation argument positions.
Boundary wires not named by `formals` are the ambient parameter vector.
-/
structure ContentOccurrence
    (source : CheckedDiagram definitions)
    (pattern : CheckedOpenDiagram definitions) where
  selection : CheckedSelection source
  occurrence : Occurrence pattern source
  formals : List source.val.WireId

namespace ContentOccurrence

def parameters
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    List source.val.WireId :=
  content.occurrence.boundaryAttachments.filter fun wire =>
    decide (wire ∉ content.formals)

def formalSigs
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    List Sig :=
  content.formals.map fun wire => (source.val.wires wire).sig

def formalBoundaryPositions?
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    Option (List Nat) :=
  content.formals.mapM fun wire =>
    (Data.Finite.indexOf?
      content.occurrence.boundaryAttachments wire).map Fin.val

def toConcreteSite
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) :
    ConcreteWireQuantifier.RelationSeverSite source where
  region := content.selection.region
  removedRegions := content.selection.allRegions
  removedNodes := content.selection.allNodes
  removedWires := content.selection.internalWires
  formals := content.formals

end ContentOccurrence

/-- Specification-only strongest relation sever input. -/
structure MonolithicRelationSeverInput
    (source : CheckedDiagram definitions) where
  orientation : Orientation
  scope : source.val.RegionId
  pattern : CheckedOpenDiagram definitions
  occurrences : List (ContentOccurrence source pattern)

/-- Specification-only strongest relation join input. -/
structure MonolithicRelationJoinInput
    (source : CheckedDiagram definitions) where
  orientation : Orientation
  wire : source.val.WireId
  content : CheckedOpenDiagram definitions
  parameters : List source.val.WireId

private def severPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

private def joinPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

private def oppositeOrientation : Orientation → Orientation
  | .forward => .backward
  | .backward => .forward

private structure CheckedSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  compiledAccepted : compileSite? source scope = some compiled
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  compiledAccepted : compileSite? source scope = some compiled
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

private def endpointMember
    (endpoint : CEndpoint nodeCount)
    (endpoints : List (CEndpoint nodeCount)) : Bool :=
  decide (endpoint ∈ endpoints)

private def listsIntersect [DecidableEq α]
    (left right : List α) : Bool :=
  left.any fun value => decide (value ∈ right)

private def occurrenceOverlaps
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (left right : ContentOccurrence source pattern) : Bool :=
  decide (left.selection.region ∈ right.selection.allRegions) ||
    decide (right.selection.region ∈ left.selection.allRegions) ||
    listsIntersect left.selection.allRegions right.selection.allRegions ||
    listsIntersect left.selection.allNodes right.selection.allNodes ||
    listsIntersect left.selection.internalWires right.selection.internalWires ||
    decide
      (left.selection.region = right.selection.region ∧
        left.selection.allRegions.isEmpty ∧
        left.selection.allNodes.isEmpty ∧
        left.selection.internalWires.isEmpty ∧
        right.selection.allRegions.isEmpty ∧
        right.selection.allNodes.isEmpty ∧
        right.selection.internalWires.isEmpty)

private def pairwiseDisjoint
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions} :
    List (ContentOccurrence source pattern) → Bool
  | [] => true
  | head :: tail =>
      tail.all (fun candidate => !occurrenceOverlaps head candidate) &&
        pairwiseDisjoint tail

/--
Checker-owned evidence for one member of a nonempty relation-sever family.
The exact boundary order and scope containment are retained with the accepted
extraction; every member uses the head occurrence's ambient parameters.
-/
private structure CheckedOccurrence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
  (scope : source.val.RegionId)
  (first content : ContentOccurrence source pattern) : Type where
  extraction :
    WireQuantifierSemantics.CheckedRelationSeverOccurrence
      content.selection content.occurrence
  boundaryExact :
    content.occurrence.boundaryAttachments =
      content.formals ++ content.parameters
  contained :
    source.val.Encloses scope content.selection.region
  parametersExact :
    content.parameters = first.parameters

private theorem checkedOccurrence_allRegions
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content)
    (region : source.val.RegionId) :
    region ∈ content.occurrence.toSelection.allRegions ↔
      region ∈ content.selection.allRegions := by
  have inputExact := checked.extraction.selection_input_eq
  have rootsExact := congrArg SelectionInput.regions inputExact
  simp only [CheckedSelection.mem_allRegions,
    CheckedSelection.IsSelectedRegion, CheckedSelection.subtreeRoots]
  rw [rootsExact]

private theorem checkedOccurrence_region
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content) :
    content.occurrence.region = content.selection.region := by
  have inputExact := checked.extraction.selection_input_eq
  have regionExact := congrArg SelectionInput.region inputExact
  rw [← Occurrence.toSelection_region]
  exact regionExact

private theorem checkedOccurrence_allNodes
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content)
    (node : source.val.NodeId) :
    node ∈ content.occurrence.toSelection.allNodes ↔
      node ∈ content.selection.allNodes := by
  have inputExact := checked.extraction.selection_input_eq
  have nodesExact := congrArg SelectionInput.nodes inputExact
  simp only [CheckedSelection.mem_allNodes,
    CheckedSelection.IsSelectedNode, CheckedSelection.directNodes]
  rw [nodesExact]
  constructor <;> intro selected
  · exact selected.elim Or.inl fun region =>
      Or.inr ((checkedOccurrence_allRegions checked _).mp region)
  · exact selected.elim Or.inl fun region =>
      Or.inr ((checkedOccurrence_allRegions checked _).mpr region)

private theorem checkedOccurrence_internalWires
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content)
    (wire : source.val.WireId) :
    wire ∈ content.occurrence.toSelection.internalWires ↔
      wire ∈ content.selection.internalWires := by
  have inputExact := checked.extraction.selection_input_eq
  have wiresExact := congrArg SelectionInput.wires inputExact
  simp only [CheckedSelection.mem_internalWires,
    CheckedSelection.IsInternal, CheckedSelection.explicitWires]
  rw [wiresExact]
  constructor <;> intro selected
  · exact selected.elim
      (fun region => Or.inl ((checkedOccurrence_allRegions checked _).mp region))
      Or.inr
  · exact selected.elim
      (fun region => Or.inl ((checkedOccurrence_allRegions checked _).mpr region))
      Or.inr

private theorem CheckedOccurrence.removedRegions_length
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content) :
    content.selection.allRegions.length =
      (pattern.val.diagram.regionsList.filter fun region =>
        decide (region ≠ pattern.val.diagram.root)).length := by
  let proper := pattern.val.diagram.regionsList.filter fun region =>
    decide (region ≠ pattern.val.diagram.root)
  let images := proper.map content.occurrence.regionMap
  have imagesNodup : images.Nodup := by
    exact ((Data.Finite.allFin_nodup _).filter _).map
      content.occurrence.regionMap (by
        intro left right different same
        exact different (content.occurrence.regionMap_injective same))
  have sameMembers : ∀ region,
      region ∈ content.selection.allRegions ↔ region ∈ images := by
    intro region
    rw [← checkedOccurrence_allRegions checked]
    rw [content.occurrence.mem_toSelection_allRegions_iff_image]
    simp [images, proper, ConcreteDiagram.regionsList,
      Data.Finite.mem_allFin]
  have permuted := Data.Finite.list_perm_of_nodup_mem_iff
    content.selection.allRegions_nodup imagesNodup sameMembers
  simpa [images, proper] using permuted.length_eq

private theorem CheckedOccurrence.removedNodes_length
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content) :
    content.selection.allNodes.length = pattern.val.diagram.nodeCount := by
  let images := pattern.val.diagram.nodesList.map content.occurrence.nodeMap
  have imagesNodup : images.Nodup := by
    exact (Data.Finite.allFin_nodup _).map content.occurrence.nodeMap (by
      intro left right different same
      exact different (content.occurrence.nodeMap_injective same))
  have sameMembers : ∀ node,
      node ∈ content.selection.allNodes ↔ node ∈ images := by
    intro node
    rw [← checkedOccurrence_allNodes checked]
    rw [content.occurrence.mem_toSelection_allNodes_iff_image]
    simp [images, ConcreteDiagram.nodesList, Data.Finite.mem_allFin]
  have permuted := Data.Finite.list_perm_of_nodup_mem_iff
    content.selection.allNodes_nodup imagesNodup sameMembers
  simpa [images, ConcreteDiagram.nodesList,
    Data.Finite.allFin_eq_finRange] using permuted.length_eq

private theorem CheckedOccurrence.removedWires_length
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first content : ContentOccurrence source pattern}
    (checked : CheckedOccurrence scope first content) :
    content.selection.internalWires.length =
      (pattern.val.diagram.wiresList.filter fun wire =>
        decide (wire ∉ pattern.val.boundary)).length := by
  let internal := pattern.val.diagram.wiresList.filter fun wire =>
    decide (wire ∉ pattern.val.boundary)
  let images := internal.map content.occurrence.wireMap
  have imagesNodup : images.Nodup := by
    apply Data.Finite.list_map_nodup_of_injective_on
      ((Data.Finite.allFin_nodup _).filter _)
    intro left right leftMember rightMember same
    exact content.occurrence.internalWire_injective left right
      (by simpa [internal, ConcreteDiagram.wiresList] using leftMember)
      (by simpa [internal, ConcreteDiagram.wiresList] using rightMember)
      same
  have sameMembers : ∀ wire,
      wire ∈ content.selection.internalWires ↔ wire ∈ images := by
    intro wire
    rw [← checkedOccurrence_internalWires checked]
    rw [content.occurrence.mem_toSelection_internalWires_iff_image]
    simp [images, internal, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin]
  have permuted := Data.Finite.list_perm_of_nodup_mem_iff
    content.selection.internalWires_nodup imagesNodup sameMembers
  simpa [images, internal] using permuted.length_eq

/-- Pointwise checked evidence for the complete durable occurrence list. -/
private inductive CheckedOccurrenceList
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first : ContentOccurrence source pattern) :
    List (ContentOccurrence source pattern) → Type
  | nil : CheckedOccurrenceList scope first []
  | cons
      {content : ContentOccurrence source pattern}
      {rest : List (ContentOccurrence source pattern)}
      (checked : CheckedOccurrence scope first content)
      (tail : CheckedOccurrenceList scope first rest) :
      CheckedOccurrenceList scope first (content :: rest)

/--
The sole retained validation receipt for one nonempty relation-sever family.
Its head owns the coherent ambient parameter vector and parameter-scope proof.
-/
private structure CheckedOccurrences
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (contents : List (ContentOccurrence source pattern)) : Type where
  first : ContentOccurrence source pattern
  rest : List (ContentOccurrence source pattern)
  contentsExact : contents = first :: rest
  entries : CheckedOccurrenceList scope first contents
  disjoint : pairwiseDisjoint contents = true
  parameterScopes :
    ∀ position : Fin first.parameters.length,
      source.val.Encloses
        (source.val.wires (first.parameters.get position)).scope scope

private def CheckedOccurrenceList.semanticEvidence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)} :
    CheckedOccurrenceList scope first contents →
      List
        (WireQuantifierSemantics.RelationSeverOccurrence source pattern)
  | .nil => []
  | .cons (content := content) checked tail =>
      { selection := content.selection
        occurrence := content.occurrence
        extraction := checked.extraction
        formals := content.formals } :: tail.semanticEvidence

private theorem CheckedOccurrenceList.semanticEvidence_sites
    (entries : CheckedOccurrenceList scope first contents) :
    entries.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site =
      contents.map ContentOccurrence.toConcreteSite := by
  induction entries with
  | nil => rfl
  | cons checked tail induction =>
      simp [CheckedOccurrenceList.semanticEvidence,
        WireQuantifierSemantics.RelationSeverOccurrence.site,
        ContentOccurrence.toConcreteSite, induction]

/-- Every proper pattern region belongs to the exact removal segment of its
checked occurrence. -/
private theorem CheckedOccurrenceList.properRegion_mem_removedRegions
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (content : ContentOccurrence source pattern)
    (member : content ∈ contents)
    (region : pattern.val.diagram.RegionId)
    (nonroot : region ≠ pattern.val.diagram.root) :
    content.occurrence.regionMap region ∈
      content.toConcreteSite.removedRegions := by
  induction entries generalizing content with
  | nil => simp at member
  | @cons head rest checked tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · change content.occurrence.regionMap region ∈
          content.selection.allRegions
        rw [← checkedOccurrence_allRegions checked]
        rw [content.occurrence.mem_toSelection_allRegions_iff_image]
        exact ⟨region, nonroot, rfl⟩
      · exact induction content member

private theorem CheckedOccurrenceList.nodeImage_mem_removedNodes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (content : ContentOccurrence source pattern)
    (member : content ∈ contents)
    (node : pattern.val.diagram.NodeId) :
    content.occurrence.nodeMap node ∈
      content.toConcreteSite.removedNodes := by
  induction entries generalizing content with
  | nil => simp at member
  | @cons head rest checked tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · change content.occurrence.nodeMap node ∈ content.selection.allNodes
        rw [← checkedOccurrence_allNodes checked]
        rw [content.occurrence.mem_toSelection_allNodes_iff_image]
        exact ⟨node, rfl⟩
      · exact induction content member

private theorem CheckedOccurrenceList.internalWireImage_mem_removedWires
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (content : ContentOccurrence source pattern)
    (member : content ∈ contents)
    (wire : pattern.val.diagram.WireId)
    (internal : wire ∉ pattern.val.boundary) :
    content.occurrence.wireMap wire ∈
      content.toConcreteSite.removedWires := by
  induction entries generalizing content with
  | nil => simp at member
  | @cons head rest checked tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · change content.occurrence.wireMap wire ∈
          content.selection.internalWires
        rw [← checkedOccurrence_internalWires checked]
        rw [content.occurrence.mem_toSelection_internalWires_iff_image]
        exact ⟨wire, internal, rfl⟩
      · exact induction content member

private theorem CheckedOccurrenceList.occurrenceRegion_eq_selectionRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (content : ContentOccurrence source pattern)
    (member : content ∈ contents) :
    content.occurrence.region = content.selection.region := by
  induction entries generalizing content with
  | nil => simp at member
  | @cons head rest checked tail induction =>
      rcases List.mem_cons.mp member with rfl | member
      · exact checkedOccurrence_region checked
      · exact induction content member

private theorem CheckedOccurrenceList.removedRegions_length
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents) :
    ((contents.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedRegions).length =
        contents.length *
          (pattern.val.diagram.regionsList.filter fun region =>
            decide (region ≠ pattern.val.diagram.root)).length := by
  induction entries with
  | nil => simp
  | cons checked tail induction =>
      simp [ContentOccurrence.toConcreteSite,
        checked.removedRegions_length, induction, Nat.succ_mul,
        Nat.add_comm, Nat.add_mul]

private theorem CheckedOccurrenceList.removedNodes_length
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents) :
    ((contents.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedNodes).length =
        contents.length * pattern.val.diagram.nodeCount := by
  induction entries with
  | nil => simp
  | cons checked tail induction =>
      simp [ContentOccurrence.toConcreteSite,
        checked.removedNodes_length, induction, Nat.succ_mul,
        Nat.add_comm, Nat.add_mul]

private theorem CheckedOccurrenceList.removedWires_length
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents) :
    ((contents.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedWires).length =
        contents.length *
          (pattern.val.diagram.wiresList.filter fun wire =>
            decide (wire ∉ pattern.val.boundary)).length := by
  induction entries with
  | nil => simp
  | cons checked tail induction =>
      simp [ContentOccurrence.toConcreteSite,
        checked.removedWires_length, induction, Nat.succ_mul,
        Nat.add_comm, Nat.add_mul]

private noncomputable def CheckedOccurrenceList.get
    (entries : CheckedOccurrenceList scope first contents)
    (position : Fin contents.length) :
    CheckedOccurrence scope first (contents.get position) := by
  induction entries with
  | nil => exact Fin.elim0 position
  | cons checked tail induction =>
      refine Fin.cases ?_ (fun rest => ?_) position
      · simpa using checked
      · simpa [List.get_eq_getElem] using induction rest

private def CheckedOccurrences.semanticEvidence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {contents : List (ContentOccurrence source pattern)}
    (checked : CheckedOccurrences scope contents) :
    List
      (WireQuantifierSemantics.RelationSeverOccurrence source pattern) :=
  checked.entries.semanticEvidence

/-!
## Batch reconstruction carrier partition

The inverse join restores a severed family in site order.  During that fold,
only the batch-retained carriers and the carriers belonging to the already
restored occurrence prefix have a representative in the current diagram.
These predicates make that partial domain explicit; the completed fold proves
that the domain is all of the original source.
-/

private def retainedBySitesRegion
    {source : CheckedDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (region : source.val.RegionId) : Prop :=
  region ∉ sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedRegions

private def retainedBySitesNode
    {source : CheckedDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (node : source.val.NodeId) : Prop :=
  node ∉ sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedNodes

private def retainedBySitesWire
    {source : CheckedDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (wire : source.val.WireId) : Prop :=
  wire ∉ sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedWires

private def restoredRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (region : source.val.RegionId) : Prop :=
  ∃ content ∈ restored, ∃ patternRegion,
    patternRegion ≠ pattern.val.diagram.root ∧
      content.occurrence.regionMap patternRegion = region

private def restoredNode
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (node : source.val.NodeId) : Prop :=
  ∃ content ∈ restored, ∃ patternNode,
    content.occurrence.nodeMap patternNode = node

private def restoredWire
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (wire : source.val.WireId) : Prop :=
  ∃ content ∈ restored, ∃ patternWire,
    patternWire ∉ pattern.val.boundary ∧
      content.occurrence.wireMap patternWire = wire

private def BatchCoveredRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (region : source.val.RegionId) : Prop :=
  retainedBySitesRegion sites region ∨ restoredRegion restored region

private def BatchCoveredNode
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (node : source.val.NodeId) : Prop :=
  retainedBySitesNode sites node ∨ restoredNode restored node

private def BatchCoveredWire
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (wire : source.val.WireId) : Prop :=
  retainedBySitesWire sites wire ∨ restoredWire restored wire

private theorem CheckedOccurrenceList.regionCoverage
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (region : source.val.RegionId) :
    BatchCoveredRegion (contents.map ContentOccurrence.toConcreteSite)
      contents region := by
  induction entries with
  | nil => exact Or.inl (by simp [retainedBySitesRegion])
  | @cons content rest checked tail induction =>
      by_cases selected : region ∈ content.selection.allRegions
      · apply Or.inr
        obtain ⟨patternRegion, nonroot, mapped⟩ :=
          content.occurrence.mem_toSelection_allRegions_iff_image region
            |>.mp ((checkedOccurrence_allRegions checked region).mpr selected)
        exact ⟨content, by simp, patternRegion, nonroot, mapped⟩
      · rcases induction with retained | restored
        · exact Or.inl (by
            simpa [retainedBySitesRegion, ContentOccurrence.toConcreteSite,
              selected] using retained)
        · rcases restored with
            ⟨candidate, member, patternRegion, nonroot, mapped⟩
          exact Or.inr
            ⟨candidate, by simp [member], patternRegion, nonroot, mapped⟩

private theorem CheckedOccurrenceList.nodeCoverage
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (node : source.val.NodeId) :
    BatchCoveredNode (contents.map ContentOccurrence.toConcreteSite)
      contents node := by
  induction entries with
  | nil => exact Or.inl (by simp [retainedBySitesNode])
  | @cons content rest checked tail induction =>
      by_cases selected : node ∈ content.selection.allNodes
      · apply Or.inr
        obtain ⟨patternNode, mapped⟩ :=
          content.occurrence.mem_toSelection_allNodes_iff_image node
            |>.mp ((checkedOccurrence_allNodes checked node).mpr selected)
        exact ⟨content, by simp, patternNode, mapped⟩
      · rcases induction with retained | restored
        · exact Or.inl (by
            simpa [retainedBySitesNode, ContentOccurrence.toConcreteSite,
              selected] using retained)
        · rcases restored with ⟨candidate, member, patternNode, mapped⟩
          exact Or.inr ⟨candidate, by simp [member], patternNode, mapped⟩

private theorem CheckedOccurrenceList.wireCoverage
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    {contents : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (wire : source.val.WireId) :
    BatchCoveredWire (contents.map ContentOccurrence.toConcreteSite)
      contents wire := by
  induction entries with
  | nil => exact Or.inl (by simp [retainedBySitesWire])
  | @cons content rest checked tail induction =>
      by_cases selected : wire ∈ content.selection.internalWires
      · apply Or.inr
        obtain ⟨patternWire, internal, mapped⟩ :=
          content.occurrence.mem_toSelection_internalWires_iff_image wire
            |>.mp ((checkedOccurrence_internalWires checked wire).mpr selected)
        exact ⟨content, by simp, patternWire, internal, mapped⟩
      · rcases induction with retained | restored
        · exact Or.inl (by
            simpa [retainedBySitesWire, ContentOccurrence.toConcreteSite,
              selected] using retained)
        · rcases restored with
            ⟨candidate, member, patternWire, internal, mapped⟩
          exact Or.inr
            ⟨candidate, by simp [member], patternWire, internal, mapped⟩

/-- In a nodup sever partition, a proper region of the next occurrence is
neither retained nor represented by any earlier occurrence. -/
private theorem properRegion_not_covered_before
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    {first : ContentOccurrence source pattern}
    {contents restored : List (ContentOccurrence source pattern)}
    (entries : CheckedOccurrenceList scope first contents)
    (sitesExact : sites = contents.map ContentOccurrence.toConcreteSite)
    (content : ContentOccurrence source pattern)
    (suffix : List (ContentOccurrence source pattern))
    (decomposition : contents = restored ++ content :: suffix)
    (region : pattern.val.diagram.RegionId)
    (nonroot : region ≠ pattern.val.diagram.root) :
    ¬ BatchCoveredRegion sites restored
      (content.occurrence.regionMap region) := by
  intro covered
  have contentMember : content ∈ contents := by
    rw [decomposition]
    simp
  have currentMember :=
    entries.properRegion_mem_removedRegions content contentMember region
      nonroot
  let prefixRemoved :=
    (restored.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedRegions
  let suffixRemoved :=
    (suffix.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedRegions
  have removedExact :
      sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedRegions =
        prefixRemoved ++ content.toConcreteSite.removedRegions ++
          suffixRemoved := by
    rw [sitesExact, decomposition]
    simp [prefixRemoved, suffixRemoved]
  rcases covered with retained | represented
  · exact retained (removedExact.symm ▸ (by
      simp [currentMember]))
  · rcases represented with
      ⟨candidate, candidateMember, candidateRegion, candidateNonroot,
        mapped⟩
    have candidateInContents : candidate ∈ contents := by
      rw [decomposition]
      exact List.mem_append.mpr (Or.inl candidateMember)
    have candidateRemoved :=
      entries.properRegion_mem_removedRegions candidate candidateInContents
        candidateRegion candidateNonroot
    have prefixMember :
        content.occurrence.regionMap region ∈ prefixRemoved := by
      rw [← mapped]
      exact List.mem_flatMap.mpr
        ⟨candidate.toConcreteSite,
          List.mem_map.mpr ⟨candidate, candidateMember, rfl⟩,
          candidateRemoved⟩
    have currentInSuffix :
        content.occurrence.regionMap region ∈
          content.toConcreteSite.removedRegions ++ suffixRemoved := by
      exact List.mem_append.mpr (Or.inl currentMember)
    have nodup :
        (prefixRemoved ++
          (content.toConcreteSite.removedRegions ++ suffixRemoved)).Nodup := by
      have fullNodup := result.removedRegions_nodup
      rw [removedExact] at fullNodup
      simpa [List.append_assoc] using fullNodup
    exact (List.nodup_append.mp nodup).2.2 _ prefixMember _
      currentInSuffix rfl

private theorem nodeImage_not_covered_before
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {first : ContentOccurrence source pattern}
    {contents restored : List (ContentOccurrence source pattern)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (entries : CheckedOccurrenceList scope first contents)
    (sitesExact : sites = contents.map ContentOccurrence.toConcreteSite)
    (content : ContentOccurrence source pattern)
    (suffix : List (ContentOccurrence source pattern))
    (decomposition : contents = restored ++ content :: suffix)
    (node : pattern.val.diagram.NodeId) :
    ¬ BatchCoveredNode sites restored
      (content.occurrence.nodeMap node) := by
  intro covered
  have contentMember : content ∈ contents := by rw [decomposition]; simp
  have currentMember := entries.nodeImage_mem_removedNodes content
    contentMember node
  let prefixRemoved :=
    (restored.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedNodes
  let suffixRemoved :=
    (suffix.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedNodes
  have removedExact :
      sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedNodes =
        prefixRemoved ++ content.toConcreteSite.removedNodes ++
          suffixRemoved := by
    rw [sitesExact, decomposition]
    simp [prefixRemoved, suffixRemoved]
  rcases covered with retained | represented
  · exact retained (removedExact.symm ▸ (by simp [currentMember]))
  · rcases represented with ⟨candidate, candidateMember, patternNode, mapped⟩
    have candidateInContents : candidate ∈ contents := by
      rw [decomposition]
      exact List.mem_append.mpr (Or.inl candidateMember)
    have candidateRemoved := entries.nodeImage_mem_removedNodes candidate
      candidateInContents patternNode
    have prefixMember : content.occurrence.nodeMap node ∈ prefixRemoved := by
      rw [← mapped]
      exact List.mem_flatMap.mpr
        ⟨candidate.toConcreteSite,
          List.mem_map.mpr ⟨candidate, candidateMember, rfl⟩,
          candidateRemoved⟩
    have currentInSuffix : content.occurrence.nodeMap node ∈
        content.toConcreteSite.removedNodes ++ suffixRemoved :=
      List.mem_append.mpr (Or.inl currentMember)
    have nodup :
        (prefixRemoved ++
          (content.toConcreteSite.removedNodes ++ suffixRemoved)).Nodup := by
      have fullNodup := result.removedNodes_nodup
      rw [removedExact] at fullNodup
      simpa [List.append_assoc] using fullNodup
    exact (List.nodup_append.mp nodup).2.2 _ prefixMember _
      currentInSuffix rfl

private theorem internalWireImage_not_covered_before
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {first : ContentOccurrence source pattern}
    {contents restored : List (ContentOccurrence source pattern)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (entries : CheckedOccurrenceList scope first contents)
    (sitesExact : sites = contents.map ContentOccurrence.toConcreteSite)
    (content : ContentOccurrence source pattern)
    (suffix : List (ContentOccurrence source pattern))
    (decomposition : contents = restored ++ content :: suffix)
    (wire : pattern.val.diagram.WireId)
    (internal : wire ∉ pattern.val.boundary) :
    ¬ BatchCoveredWire sites restored
      (content.occurrence.wireMap wire) := by
  intro covered
  have contentMember : content ∈ contents := by rw [decomposition]; simp
  have currentMember := entries.internalWireImage_mem_removedWires content
    contentMember wire internal
  let prefixRemoved :=
    (restored.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedWires
  let suffixRemoved :=
    (suffix.map ContentOccurrence.toConcreteSite).flatMap
      ConcreteWireQuantifier.RelationSeverSite.removedWires
  have removedExact :
      sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedWires =
        prefixRemoved ++ content.toConcreteSite.removedWires ++
          suffixRemoved := by
    rw [sitesExact, decomposition]
    simp [prefixRemoved, suffixRemoved]
  rcases covered with retained | represented
  · exact retained (removedExact.symm ▸ (by simp [currentMember]))
  · rcases represented with
      ⟨candidate, candidateMember, patternWire, candidateInternal, mapped⟩
    have candidateInContents : candidate ∈ contents := by
      rw [decomposition]
      exact List.mem_append.mpr (Or.inl candidateMember)
    have candidateRemoved :=
      entries.internalWireImage_mem_removedWires candidate
        candidateInContents patternWire candidateInternal
    have prefixMember : content.occurrence.wireMap wire ∈ prefixRemoved := by
      rw [← mapped]
      exact List.mem_flatMap.mpr
        ⟨candidate.toConcreteSite,
          List.mem_map.mpr ⟨candidate, candidateMember, rfl⟩,
          candidateRemoved⟩
    have currentInSuffix : content.occurrence.wireMap wire ∈
        content.toConcreteSite.removedWires ++ suffixRemoved :=
      List.mem_append.mpr (Or.inl currentMember)
    have nodup :
        (prefixRemoved ++
          (content.toConcreteSite.removedWires ++ suffixRemoved)).Nodup := by
      have fullNodup := result.removedWires_nodup
      rw [removedExact] at fullNodup
      simpa [List.append_assoc] using fullNodup
    exact (List.nodup_append.mp nodup).2.2 _ prefixMember _
      currentInSuffix rfl

/-- Construction state for the snoc induction restoring a severed family. -/
private theorem denseIndex_injective
    [DecidableEq α]
    (values : List α)
    {left right : α}
    (leftMember : left ∈ values)
    (rightMember : right ∈ values)
    (same : DenseList.index values left leftMember =
      DenseList.index values right rightMember) :
    left = right := by
  have mapped := congrArg values.get same
  rw [DenseList.get_index, DenseList.get_index] at mapped
  exact mapped

private def PortDataCorresponds
    (left : CNode leftRegionCount definitionCount)
    (right : CNode rightRegionCount definitionCount)
    (leftPort rightPort : CPort) : Prop :=
  match left, right with
  | .identity _ leftSig leftArity, .identity _ rightSig rightArity =>
      leftSig = rightSig ∧ leftArity = rightArity ∧
        ∃ leftIndex rightIndex,
          leftPort = .identity leftIndex ∧ rightPort = .identity rightIndex
  | _, _ => rightPort = leftPort

private def requiredPortsForNode
    (node : CNode regionCount definitionCount) : List CPort :=
  match node with
  | .atom _ args => CPort.head :: (List.range args.length).map CPort.arg
  | .ref _ _ args => (List.range args.length).map CPort.arg
  | .identity _ _ arity => (List.range arity).map CPort.identity

@[simp] private theorem requiredPortsForNode_relocate
    (node : CNode regionCount definitionCount)
    (region : Fin targetRegionCount) :
    requiredPortsForNode (node.relocate region) = requiredPortsForNode node := by
  cases node <;> rfl

private theorem portDataCorresponds_refl_relocate
    (diagram : ConcreteDiagram definitionCount)
    (node : diagram.NodeId)
    (region : Fin targetRegionCount)
    (port : CPort)
    (required : port ∈ diagram.requiredPorts node) :
    PortDataCorresponds (diagram.nodes node)
      ((diagram.nodes node).relocate region) port port := by
  cases data : diagram.nodes node with
  | atom sourceRegion args => simp [PortDataCorresponds, CNode.relocate, data]
  | ref sourceRegion definition args =>
      simp [PortDataCorresponds, CNode.relocate, data]
  | identity sourceRegion sig arity =>
      have identityRequired :
          port ∈ (List.range arity).map CPort.identity := by
        simpa [ConcreteDiagram.requiredPorts, data] using required
      obtain ⟨index, member, rfl⟩ := List.mem_map.mp identityRequired
      exact ⟨rfl, rfl, index, index, rfl, rfl⟩

private structure BatchReconstructionState
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (current : CheckedDiagram definitions)
    (joinSource : CheckedDiagram definitions) where
  regionImage :
    { region : source.val.RegionId //
        BatchCoveredRegion sites restored region } →
      current.val.RegionId
  regionImage_injective : Function.Injective regionImage
  retainedRegionImage_val :
    ∀ region (retained : retainedBySitesRegion sites region),
      (regionImage ⟨region, Or.inl retained⟩).val =
        (ConcreteWireQuantifier.Internal.retainedRegionIndex source
          (sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedRegions)
          region (by
            apply List.mem_filter.mpr
            exact ⟨by
              simp [ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin], decide_eq_true retained⟩)).val
  regionParentCovered :
    ∀ region : { region : source.val.RegionId //
        BatchCoveredRegion sites restored region },
      ∀ parent,
        source.val.regions region.1 = .cut parent →
          BatchCoveredRegion sites restored parent
  regionSheetExact :
    ∀ region : { region : source.val.RegionId //
        BatchCoveredRegion sites restored region },
      source.val.regions region.1 = .sheet →
        current.val.regions (regionImage region) = .sheet
  regionCutExact :
    ∀ region : { region : source.val.RegionId //
        BatchCoveredRegion sites restored region },
      ∀ parent (data : source.val.regions region.1 = .cut parent),
        current.val.regions (regionImage region) =
          .cut (regionImage
            ⟨parent, regionParentCovered region parent data⟩)
  nodeImage :
    { node : source.val.NodeId //
        BatchCoveredNode sites restored node } →
      current.val.NodeId
  nodeImage_injective : Function.Injective nodeImage
  nodeRegionCovered :
    ∀ node : { node : source.val.NodeId //
        BatchCoveredNode sites restored node },
      BatchCoveredRegion sites restored (source.val.nodes node.1).region
  nodeTableExact :
    ∀ node : { node : source.val.NodeId //
        BatchCoveredNode sites restored node },
      current.val.nodes (nodeImage node) =
        (source.val.nodes node.1).relocate
          (regionImage
            ⟨(source.val.nodes node.1).region, nodeRegionCovered node⟩)
  portImage :
    { node : source.val.NodeId //
        BatchCoveredNode sites restored node } →
      Data.Finite.FiniteEquiv CPort CPort
  portImageCorresponds :
    ∀ (node : { node : source.val.NodeId //
          BatchCoveredNode sites restored node })
      (port : CPort)
      (required : port ∈ source.val.requiredPorts node.1),
      PortDataCorresponds (source.val.nodes node.1)
        (current.val.nodes (nodeImage node))
        port (portImage node port)
  portImageRequired :
    ∀ (node : { node : source.val.NodeId //
          BatchCoveredNode sites restored node })
      (port : CPort),
      portImage node port ∈
          requiredPortsForNode (current.val.nodes (nodeImage node)) ↔
        port ∈ requiredPortsForNode (source.val.nodes node.1)
  wireImage :
    { wire : source.val.WireId //
        BatchCoveredWire sites restored wire } →
      current.val.WireId
  wireImage_injective : Function.Injective wireImage
  retainedWireImage_val :
    ∀ wire (retained : retainedBySitesWire sites wire),
      (wireImage ⟨wire, Or.inl retained⟩).val =
        (ConcreteWireQuantifier.Internal.retainedWireIndex source
          (sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedWires)
          wire (by
            apply List.mem_filter.mpr
            exact ⟨by simp [ConcreteDiagram.wiresList,
              Data.Finite.mem_allFin], decide_eq_true retained⟩)).val
  wireScopeCovered :
    ∀ wire : { wire : source.val.WireId //
        BatchCoveredWire sites restored wire },
      BatchCoveredRegion sites restored (source.val.wires wire.1).scope
  wireSignatureExact :
    ∀ wire : { wire : source.val.WireId //
        BatchCoveredWire sites restored wire },
      (current.val.wires (wireImage wire)).sig =
        (source.val.wires wire.1).sig
  wireScopeExact :
    ∀ wire : { wire : source.val.WireId //
        BatchCoveredWire sites restored wire },
      (current.val.wires (wireImage wire)).scope =
        regionImage
          ⟨(source.val.wires wire.1).scope, wireScopeCovered wire⟩
  wireEndpointForward :
    ∀ (wire : { wire : source.val.WireId //
          BatchCoveredWire sites restored wire })
      (endpoint : CEndpoint source.val.nodeCount)
      (incident : endpoint ∈ (source.val.wires wire.1).endpoints)
      (nodeCovered : BatchCoveredNode sites restored endpoint.node),
      ({ node := nodeImage ⟨endpoint.node, nodeCovered⟩
         port := portImage ⟨endpoint.node, nodeCovered⟩ endpoint.port } :
          CEndpoint current.val.nodeCount) ∈
        (current.val.wires (wireImage wire)).endpoints
  joinNodeImage : joinSource.val.NodeId → Option current.val.NodeId
  pendingOrigins : List joinSource.val.NodeId
  pendingApplications : List current.val.NodeId
  pendingApplicationsExact :
    pendingApplications = pendingOrigins.filterMap joinNodeImage
  representedNodesAvoidPending :
    ∀ node :
        { node : source.val.NodeId //
          BatchCoveredNode sites restored node },
      nodeImage node ∉ pendingApplications

namespace BatchReconstructionState

/-- Total region map once the restored prefix is the complete checked family. -/
private def completeRegionImage
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {contents : List (ContentOccurrence source pattern)}
    {current : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    (state : BatchReconstructionState
      (contents.map ContentOccurrence.toConcreteSite) contents current
        joinSource)
    (entries : CheckedOccurrenceList scope first contents) :
    source.val.RegionId → current.val.RegionId :=
  fun region => state.regionImage ⟨region, entries.regionCoverage region⟩

/-- Total node map once the restored prefix is the complete checked family. -/
private def completeNodeImage
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {contents : List (ContentOccurrence source pattern)}
    {current : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    (state : BatchReconstructionState
      (contents.map ContentOccurrence.toConcreteSite) contents current
        joinSource)
    (entries : CheckedOccurrenceList scope first contents) :
    source.val.NodeId → current.val.NodeId :=
  fun node => state.nodeImage ⟨node, entries.nodeCoverage node⟩

/-- Total wire map once the restored prefix is the complete checked family. -/
private def completeWireImage
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {contents : List (ContentOccurrence source pattern)}
    {current : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {first : ContentOccurrence source pattern}
    (state : BatchReconstructionState
      (contents.map ContentOccurrence.toConcreteSite) contents current
        joinSource)
    (entries : CheckedOccurrenceList scope first contents) :
    source.val.WireId → current.val.WireId :=
  fun wire => state.wireImage ⟨wire, entries.wireCoverage wire⟩

end BatchReconstructionState

private def formalBoundaryValid
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) : Bool :=
  content.formals.all fun wire =>
    decide (wire ∈ content.occurrence.boundaryAttachments)

private def parametersEnclose
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (parameters : List source.val.WireId) : Bool :=
  parameters.all fun wire =>
    decide (source.val.Encloses (source.val.wires wire).scope scope)

private theorem parametersEnclose_of_true
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (parameters : List source.val.WireId)
    (accepted : parametersEnclose source scope parameters = true) :
    ∀ position : Fin parameters.length,
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope scope := by
  intro position
  have member :
      parameters.get position ∈ parameters :=
    List.get_mem parameters position
  have checked :
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope scope := by
    exact
      List.all_eq_true.mp (by
        simpa [parametersEnclose] using accepted)
        (parameters.get position) member
  exact checked

private def boundarySigs
    (content : CheckedOpenDiagram definitions) : List Sig :=
  content.val.boundary.map fun wire =>
    (content.val.diagram.wires wire).sig

private def splitAt? (count : Nat) (values : List α) :
    Option (List α × List α) :=
  if count ≤ values.length then
    some (values.take count, values.drop count)
  else
    none

private structure RelationApplication
    (source : CheckedDiagram definitions)
    (args : List Sig) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId

private def argumentWires?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    List Sig → Nat → Option (List source.val.WireId)
  | [], _ => some []
  | expected :: rest, index => do
      let wire ← source.val.endpointOwner? ⟨node, .arg index⟩
      if (source.val.wires wire).sig = expected then
        let tail ← argumentWires? source node rest (index + 1)
        pure (wire :: tail)
      else
        none

private def applicationAt?
    (source : CheckedDiagram definitions)
    (relation : source.val.WireId)
    (args : List Sig)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (RelationApplication source args) := do
  if endpoint.port = .head then pure () else none
  match source.val.nodes endpoint.node with
  | .atom region nodeArgs =>
      if nodeArgs = args then
        if source.val.Encloses (source.val.wires relation).scope region then
          let arguments ← argumentWires? source endpoint.node args 0
          pure { node := endpoint.node, region := region, arguments := arguments }
        else
          none
      else
        none
  | _ => none

private def collectApplications?
    (source : CheckedDiagram definitions)
    (relation : source.val.WireId)
    (args : List Sig) :
    Option (List (RelationApplication source args)) := do
  let applications ←
    (source.val.wires relation).endpoints.mapM
      (applicationAt? source relation args)
  if applications.map (·.node) |>.Nodup then
    pure applications
  else
    none

private structure CheckedOpenCompilation
    (content : CheckedOpenDiagram definitions) where
  compilation : OpenCompilation content
  accepted : compileOpen content = some compilation

private structure CheckedRelationJoin
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) where
  arguments : List Sig
  sourceSignature : (source.val.wires wire).sig = .rel arguments
  boundaryLength :
    content.val.boundary.length = arguments.length + parameters.length
  formalSignatures :
    (content.val.boundary.take arguments.length).map
        (fun boundaryWire => (content.val.diagram.wires boundaryWire).sig) =
      arguments
  parameterSignatures :
    (content.val.boundary.drop arguments.length).map
        (fun boundaryWire => (content.val.diagram.wires boundaryWire).sig) =
      parameters.map (fun parameter => (source.val.wires parameter).sig)
  liveNotParameter : wire ∉ parameters
  polarity :
    CheckedJoinPolarity source orientation
      (source.val.wires wire).scope
  applications : List source.val.NodeId
  contentCompilation : CheckedOpenCompilation content
  parameterScopes :
    ∀ position : Fin parameters.length,
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope
        (source.val.wires wire).scope

private structure RelationJoinReceipt
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (target : CheckedDiagram definitions)
    (applications : List source.val.NodeId) where
  arguments : List Sig
  sourceSignature : (source.val.wires wire).sig = .rel arguments
  boundaryLength :
    content.val.boundary.length = arguments.length + parameters.length
  formalSignatures :
    (content.val.boundary.take arguments.length).map
        (fun boundaryWire => (content.val.diagram.wires boundaryWire).sig) =
      arguments
  parameterSignatures :
    (content.val.boundary.drop arguments.length).map
        (fun boundaryWire => (content.val.diagram.wires boundaryWire).sig) =
      parameters.map (fun parameter => (source.val.wires parameter).sig)
  liveNotParameter : wire ∉ parameters
  polarity :
    CheckedJoinPolarity source orientation
      (source.val.wires wire).scope
  contentCompilation : CheckedOpenCompilation content
  result :
    ConcreteWireQuantifier.RelationJoinResult source wire content parameters
  accepted :
    ConcreteWireQuantifier.joinRelation source wire content parameters =
      .ok result
  targetExact : target = result.checked
  applicationsExact : applications = result.applications
  parameterScopes :
    ∀ position : Fin parameters.length,
      source.val.Encloses
        (source.val.wires (parameters.get position)).scope
        (source.val.wires wire).scope

private structure RelationSeverConcreteReceipt
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId)
    (pattern : CheckedOpenDiagram definitions)
    (occurrences : List (ContentOccurrence source pattern))
    (target : CheckedDiagram definitions) where
  extractions : CheckedOccurrences scope occurrences
  result :
    ConcreteWireQuantifier.RelationSeverResult source scope
      (extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site)
  accepted :
    ConcreteWireQuantifier.severRelation source scope
        (extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site) =
      .ok result
  targetExact : target = result.checked
  parameters : List result.checked.val.WireId
  parametersAccepted :
    extractions.first.parameters.mapM result.wireImage? = some parameters
  inverseChecked :
    CheckedRelationJoin result.checked (oppositeOrientation orientation)
      result.relationWire pattern parameters
  inverse :
    ConcreteWireQuantifier.RelationJoinResult result.checked
      result.relationWire pattern parameters
  inverseAccepted :
    ConcreteWireQuantifier.joinRelation result.checked result.relationWire
        pattern parameters =
      .ok inverse
  inverseStepsExact :
    inverse.steps.map ConcreteWireQuantifier.RelationJoinStep.application =
      result.atoms
  inverseIso : ConcreteIso inverse.plainFinal.val source.val

/-- Nil case of the batch reconstruction fold: only sever-retained carriers
have representatives before the first occurrence is restored. -/
private def batchReconstructionNil
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites) :
    BatchReconstructionState (pattern := pattern) sites [] result.checked
      result.checked where
  regionImage := fun region =>
    result.regionImage region.1 (by
      have retained :
          region.1 ∉
            sites.flatMap
              ConcreteWireQuantifier.RelationSeverSite.removedRegions := by
        simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
          using region.2
      exact (result.retainedRegion_iff region.1).mpr retained)
  regionImage_injective := by
    intro left right same
    apply Subtype.ext
    apply denseIndex_injective
      (ConcreteWireQuantifier.Internal.retainedRegions source
        (sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedRegions))
      (by
        exact (result.retainedRegion_iff left.1).mpr (by
          simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
            using left.2))
      (by
        exact (result.retainedRegion_iff right.1).mpr (by
          simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
            using right.2))
    apply Fin.ext
    simpa using congrArg Fin.val same
  retainedRegionImage_val := by
    intro region retained
    rfl
  regionParentCovered := by
    intro region parent data
    apply Or.inl
    have regionRetained := (result.retainedRegion_iff region.1).mpr (by
      simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
        using region.2)
    exact (result.retainedRegion_iff parent).mp
      (result.regionParent_survives region.1 regionRetained parent data)
  regionSheetExact := by
    intro region data
    apply result.regionImage_sheet region.1
      ((result.retainedRegion_iff region.1).mpr (by
        simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
          using region.2))
    exact data
  regionCutExact := by
    intro region parent data
    apply result.regionImage_cut region.1
      ((result.retainedRegion_iff region.1).mpr (by
        simpa [BatchCoveredRegion, restoredRegion, retainedBySitesRegion]
          using region.2))
      parent data
  nodeImage := fun node =>
    result.nodeImage node.1 (by
      have retained :
          node.1 ∉
            sites.flatMap
              ConcreteWireQuantifier.RelationSeverSite.removedNodes := by
        simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
          using node.2
      exact (result.retainedNode_iff node.1).mpr retained)
  nodeImage_injective := by
    intro left right same
    apply Subtype.ext
    apply denseIndex_injective
      (ConcreteWireQuantifier.Internal.retainedNodes source
        (sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedNodes))
      (by
        exact (result.retainedNode_iff left.1).mpr (by
          simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
            using left.2))
      (by
        exact (result.retainedNode_iff right.1).mpr (by
          simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
            using right.2))
    apply Fin.ext
    simpa using congrArg Fin.val same
  nodeRegionCovered := by
    intro node
    apply Or.inl
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    exact (result.retainedRegion_iff _).mp
      (result.nodeRegion_survives node.1 nodeRetained)
  nodeTableExact := by
    intro node
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    exact result.nodeImage_data node.1 nodeRetained
  portImage := fun _ => Data.Finite.FiniteEquiv.refl CPort
  portImageCorresponds := by
    intro node port required
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    rw [result.nodeImage_data node.1 nodeRetained]
    exact portDataCorresponds_refl_relocate
      source.val node.1 _ port required
  portImageRequired := by
    intro node port
    have nodeRetained := (result.retainedNode_iff node.1).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2)
    rw [result.nodeImage_data node.1 nodeRetained]
    simp
  wireImage := fun wire =>
    result.wireImage wire.1 (by
      have retained :
          wire.1 ∉
            sites.flatMap
              ConcreteWireQuantifier.RelationSeverSite.removedWires := by
        simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
          using wire.2
      exact (result.retainedWire_iff wire.1).mpr retained)
  wireImage_injective := by
    intro left right same
    apply Subtype.ext
    apply denseIndex_injective
      (ConcreteWireQuantifier.Internal.retainedWires source
        (sites.flatMap
          ConcreteWireQuantifier.RelationSeverSite.removedWires))
      (by
        exact (result.retainedWire_iff left.1).mpr (by
          simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
            using left.2))
      (by
        exact (result.retainedWire_iff right.1).mpr (by
          simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
            using right.2))
    apply Fin.ext
    simpa using congrArg Fin.val same
  retainedWireImage_val := by
    intro wire retained
    rfl
  wireScopeCovered := by
    intro wire
    apply Or.inl
    have wireRetained := (result.retainedWire_iff wire.1).mpr (by
      simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
        using wire.2)
    exact (result.retainedRegion_iff _).mp
      (result.wireScope_survives wire.1 wireRetained)
  wireSignatureExact := by
    intro wire
    exact result.wireImage_signature wire.1
      ((result.retainedWire_iff wire.1).mpr (by
        simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
          using wire.2))
  wireScopeExact := by
    intro wire
    exact result.wireImage_scope wire.1
      ((result.retainedWire_iff wire.1).mpr (by
        simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
          using wire.2))
  wireEndpointForward := by
    intro wire endpoint incident nodeCovered
    have wireRetained := (result.retainedWire_iff wire.1).mpr (by
      simpa [BatchCoveredWire, restoredWire, retainedBySitesWire]
        using wire.2)
    have nodeRetained := (result.retainedNode_iff endpoint.node).mpr (by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using nodeCovered)
    exact result.wireImage_endpoint_mem wire.1 wireRetained endpoint
      nodeRetained incident
  joinNodeImage := fun node => some node
  pendingOrigins := result.atoms
  pendingApplications := result.atoms
  pendingApplicationsExact := by simp
  representedNodesAvoidPending := by
    intro node pending
    have retained :
        node.1 ∉
          sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedNodes := by
      simpa [BatchCoveredNode, restoredNode, retainedBySitesNode]
        using node.2
    have retainedMember := (result.retainedNode_iff node.1).mpr retained
    unfold ConcreteWireQuantifier.RelationSeverResult.atoms at pending
    rcases List.mem_map.mp pending with ⟨site, _siteMember, atomExact⟩
    have values := congrArg Fin.val atomExact
    rw [result.atom_val] at values
    rw [result.nodeImage_val node.1 retainedMember] at values
    have imageBound :=
      result.nodeImage_lt_retainedCount node.1 retainedMember
    omega

private theorem newlyCoveredRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    (content : ContentOccurrence source pattern)
    (region : source.val.RegionId)
    (covered : BatchCoveredRegion sites (restored ++ [content]) region)
    (notOld : ¬ BatchCoveredRegion sites restored region) :
    ∃ patternRegion,
      patternRegion ≠ pattern.val.diagram.root ∧
        content.occurrence.regionMap patternRegion = region := by
  rcases covered with retained | restoredAll
  · exact False.elim (notOld (Or.inl retained))
  · rcases restoredAll with
      ⟨candidate, member, patternRegion, nonroot, mapped⟩
    rcases List.mem_append.mp member with previous | final
    · exact False.elim
        (notOld (Or.inr
          ⟨candidate, previous, patternRegion, nonroot, mapped⟩))
    · have candidateExact : candidate = content := by simpa using final
      subst candidate
      exact ⟨patternRegion, nonroot, mapped⟩

private theorem newlyCoveredNode
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    (content : ContentOccurrence source pattern)
    (node : source.val.NodeId)
    (covered : BatchCoveredNode sites (restored ++ [content]) node)
    (notOld : ¬ BatchCoveredNode sites restored node) :
    ∃ patternNode, content.occurrence.nodeMap patternNode = node := by
  rcases covered with retained | restoredAll
  · exact False.elim (notOld (Or.inl retained))
  · rcases restoredAll with ⟨candidate, member, patternNode, mapped⟩
    rcases List.mem_append.mp member with previous | final
    · exact False.elim
        (notOld (Or.inr ⟨candidate, previous, patternNode, mapped⟩))
    · have candidateExact : candidate = content := by simpa using final
      subst candidate
      exact ⟨patternNode, mapped⟩

private theorem newlyCoveredWire
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    (content : ContentOccurrence source pattern)
    (wire : source.val.WireId)
    (covered : BatchCoveredWire sites (restored ++ [content]) wire)
    (notOld : ¬ BatchCoveredWire sites restored wire) :
    ∃ patternWire,
      patternWire ∉ pattern.val.boundary ∧
        content.occurrence.wireMap patternWire = wire := by
  rcases covered with retained | restoredAll
  · exact False.elim (notOld (Or.inl retained))
  · rcases restoredAll with
      ⟨candidate, member, patternWire, internal, mapped⟩
    rcases List.mem_append.mp member with previous | final
    · exact False.elim
        (notOld (Or.inr
          ⟨candidate, previous, patternWire, internal, mapped⟩))
    · have candidateExact : candidate = content := by simpa using final
      subst candidate
      exact ⟨patternWire, internal, mapped⟩

/-- A successful option-valued list traversal retains exact positional
ownership; consumers need not inspect the traversal implementation again. -/
private theorem optionMapM_eq_some_length_get
    {α β : Type}
    (transform : α → Option β)
    {source : List α}
    {target : List β}
    (accepted : source.mapM transform = some target) :
    ∃ exactLength : source.length = target.length,
      ∀ position : Fin source.length,
        transform (source.get position) =
          some (target.get (Fin.cast exactLength position)) := by
  induction source generalizing target with
  | nil =>
      simp at accepted
      subst target
      refine ⟨rfl, ?_⟩
      intro position
      exact Fin.elim0 position
  | cons head tail induction =>
      cases headExact : transform head with
      | none => simp [List.mapM_cons, headExact] at accepted
      | some image =>
          cases tailExact : tail.mapM transform with
          | none => simp [List.mapM_cons, headExact, tailExact] at accepted
          | some images =>
              simp [List.mapM_cons, headExact, tailExact] at accepted
              subst target
              obtain ⟨tailLength, tailEvidence⟩ := induction tailExact
              refine ⟨by simp [tailLength], ?_⟩
              intro position
              refine Fin.cases ?_ (fun rest => ?_) position
              · simpa using headExact
              · simpa [List.get_eq_getElem, tailLength] using
                  tailEvidence rest

private theorem optionMapM_eq_some_of_pointwise
    {α β : Type}
    (transform : α → Option β)
    (image : α → β)
    (values : List α)
    (pointwise : ∀ value, value ∈ values →
      transform value = some (image value)) :
    values.mapM transform = some (values.map image) := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.mapM_cons, pointwise head (by simp)]
      rw [induction (fun value member => pointwise value (by simp [member]))]
      rfl

/-- The sever result transports one site's ordered formal vector exactly to
the stored formal-image vector. -/
private theorem relationSeverSiteFormals_mapM
    {source : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    (sites.get site).formals.mapM result.wireImage? =
      some (result.siteFormalImages site) := by
  let survives :
      ∀ wire, wire ∈ (sites.get site).formals →
        wire ∈ ConcreteWireQuantifier.Internal.retainedWires source
          (sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedWires) :=
    fun wire member => by
      obtain ⟨position, rfl⟩ := List.get_of_mem member
      exact result.siteFormal_survives site position
  let image : source.val.WireId → result.checked.val.WireId :=
    fun wire =>
      if member : wire ∈ (sites.get site).formals then
        result.wireImage wire (survives wire member)
      else
        result.relationWire
  have pointwise :
      ∀ wire, wire ∈ (sites.get site).formals →
        result.wireImage? wire = some (image wire) := by
    intro wire member
    have imageExact :
        image wire = result.wireImage wire (survives wire member) := by
      unfold image
      rw [dif_pos member]
    rw [imageExact]
    simp [ConcreteWireQuantifier.RelationSeverResult.wireImage?,
      survives wire member]
  rw [optionMapM_eq_some_of_pointwise result.wireImage? image _ pointwise]
  congr 1
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    rw [result.siteFormalImages_get site ⟨index, rightBound⟩]
    simp [List.get_eq_getElem, image]

/-- Every retained semantic step carries the batch-wide relation signature
and ambient parameter vector fixed by its accepted trace. -/
private theorem relationJoinTrace_step_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List
      (ConcreteWireQuantifier.RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {regionImage : source.val.RegionId → final.val.RegionId}
    {nodeImage : source.val.NodeId → Option final.val.NodeId}
    {wireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      source dying content parameters args steps final regionImage nodeImage
        wireImage finalDying finalScope)
    (step : ConcreteWireQuantifier.RelationJoinStep source dying content)
    (member : step ∈ steps) :
    step.relationArgs = args ∧ step.sourceParameters = parameters := by
  induction trace with
  | nil => simp at member
  | snoc trace finalStep priorExact priorRegionExact priorNodeExact
      priorWireExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      rcases List.mem_append.mp member with previous | final
      · exact induction previous
      · have stepExact : step = finalStep := by simpa using final
        subst step
        exact ⟨relationArgsExact, sourceParametersExact⟩

private theorem relationJoinTrace_count_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List
      (ConcreteWireQuantifier.RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {regionImage : source.val.RegionId → final.val.RegionId}
    {nodeImage : source.val.NodeId → Option final.val.NodeId}
    {wireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      source dying content parameters args steps final regionImage nodeImage
        wireImage finalDying finalScope)
    (identitiesEmpty : ∀ step ∈ steps,
      step.attachment.identityRequests = []) :
    final.val.regionCount = source.val.regionCount +
        steps.length *
          (content.val.diagram.regionsList.filter fun region =>
            decide (region ≠ content.val.diagram.root)).length ∧
      final.val.nodeCount + steps.length = source.val.nodeCount +
        steps.length * content.val.diagram.nodeCount ∧
      final.val.wireCount = source.val.wireCount +
        steps.length *
          (content.val.diagram.wiresList.filter fun wire =>
            decide (wire ∉ content.val.boundary)).length := by
  induction trace with
  | nil => simp
  | snoc trace step priorExact priorRegionExact priorNodeExact priorWireExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      induction =>
      cases priorExact
      have stepIdentities : step.attachment.identityRequests = [] :=
        identitiesEmpty step (by simp)
      rcases induction (fun prior member =>
        identitiesEmpty prior (List.mem_append_left _ member)) with
        ⟨regionsExact, nodesExact, wiresExact⟩
      simp only [decide_not] at *
      constructor
      · have stepRegions := step.checked_regionCount
        change step.checked.val.regionCount = step.prior.val.regionCount +
          (content.val.diagram.regionsList.filter fun region =>
            decide (region ≠ content.val.diagram.root)).length at stepRegions
        simp only [decide_not] at stepRegions
        simp only [List.length_append, List.length_singleton] at *
        simp [Nat.add_mul]
        omega
      · constructor
        · have stepNodes := step.checked_nodeCount_add_one
          simp [stepIdentities] at stepNodes
          simp only [List.length_append, List.length_singleton] at *
          simp [Nat.add_mul]
          omega
        · have stepWires := step.checked_wireCount
          change step.checked.val.wireCount = step.prior.val.wireCount +
            (content.val.diagram.wiresList.filter fun wire =>
              decide (wire ∉ content.val.boundary)).length at stepWires
          simp only [decide_not] at stepWires
          simp only [List.length_append, List.length_singleton] at *
          simp [Nat.add_mul]
          omega

/-- Positional alignment between one inverse join step and the original
checked occurrence restored at that step. -/
private structure InverseStepOccurrenceAlignment
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    {dying : result.checked.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep
      result.checked dying pattern)
    (content : ContentOccurrence source pattern) where
  site : Fin sites.length
  siteExact : sites.get site = content.toConcreteSite
  applicationExact : step.application = result.atom site
  boundarySurvives :
    ∀ position : Fin pattern.val.boundary.length,
      content.occurrence.wireMap (pattern.val.boundary.get position) ∈
        ConcreteWireQuantifier.Internal.retainedWires source
          (sites.flatMap
            ConcreteWireQuantifier.RelationSeverSite.removedWires)
  sourceAttachmentExact :
    ∀ position : Fin pattern.val.boundary.length,
      step.sourceAttachments.get
          (Fin.cast step.sourceAttachmentArity.symm position) =
        result.wireImage
          (content.occurrence.wireMap
            (pattern.val.boundary.get position))
          (boundarySurvives position)

private theorem inverseStep_sourceArguments_exact
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    {dying : result.checked.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep
      result.checked dying pattern)
    (site : Fin sites.length)
    (applicationExact : step.application = result.atom site)
    (arityExact :
      (sites.get site).formals.length = step.relationArgs.length) :
    step.sourceArguments = result.siteFormalImages site := by
  have sourceLength :=
    ConcreteWireQuantifier.relationArgumentWires?_length result.checked
      step.application step.relationArgs 0 step.sourceArguments
        step.sourceArgumentsAccepted
  apply List.ext_get
  · calc
      step.sourceArguments.length = step.relationArgs.length := sourceLength
      _ = (sites.get site).formals.length := arityExact.symm
      _ = (result.siteFormalImages site).length :=
        (result.siteFormalImages_length site).symm
  · intro index sourceBound targetBound
    let argumentPosition : Fin step.relationArgs.length :=
      ⟨index, by simpa [sourceLength] using sourceBound⟩
    let formalPosition : Fin (sites.get site).formals.length :=
      Fin.cast arityExact.symm argumentPosition
    have sourceOwner :=
      ConcreteWireQuantifier.relationArgumentWires?_owner result.checked
        step.application step.relationArgs 0 step.sourceArguments
          step.sourceArgumentsAccepted argumentPosition
    have formalOwner :
        result.checked.val.endpointOwner?
            ⟨result.atom site, .arg formalPosition.val⟩ =
          some
            (result.wireImage
              ((sites.get site).formals.get formalPosition)
              (result.siteFormal_survives site formalPosition)) :=
      have incident := result.atomArgument_incident site formalPosition
      have required :=
        ConcreteDiagram.incident_port_required definitions
          result.checked.val result.checked.property _ _ incident
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        result.checked.val result.checked.property _ _ required _ incident
    have sourceOwnerAtAtom :
        result.checked.val.endpointOwner?
            ⟨result.atom site, .arg argumentPosition.val⟩ =
          some
            (step.sourceArguments.get
              (Fin.cast sourceLength.symm argumentPosition)) := by
      simpa only [applicationExact, Nat.zero_add] using sourceOwner
    have ownerSame := Option.some.inj (sourceOwnerAtAtom.symm.trans (by
      simpa [argumentPosition, formalPosition] using formalOwner))
    rw [result.siteFormalImages_get site ⟨index, targetBound⟩]
    simpa [argumentPosition, formalPosition, List.get_eq_getElem] using
      ownerSame

/-- The checker-owned occurrence evidence and accepted sever transport
determine the complete source attachment vector for its paired inverse step. -/
private noncomputable def inverseStepOccurrenceAlignmentOfChecked
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (first content : ContentOccurrence source pattern)
    (checked : CheckedOccurrence scope first content)
    (parameters : List result.checked.val.WireId)
    (parametersAccepted :
      first.parameters.mapM result.wireImage? = some parameters)
    {dying : result.checked.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep
      result.checked dying pattern)
    (site : Fin sites.length)
    (siteExact : sites.get site = content.toConcreteSite)
    (applicationExact : step.application = result.atom site)
    (arityExact :
      (sites.get site).formals.length = step.relationArgs.length)
    (sourceParametersExact : step.sourceParameters = parameters) :
    InverseStepOccurrenceAlignment result step content := by
  have siteFormalsExact :
      (sites.get site).formals = content.formals := by
    exact congrArg
      ConcreteWireQuantifier.RelationSeverSite.formals siteExact
  have sourceArgumentsExact :=
    inverseStep_sourceArguments_exact result step site applicationExact
      arityExact
  have formalsAccepted :
      content.formals.mapM result.wireImage? =
        some step.sourceArguments := by
    calc
      content.formals.mapM result.wireImage? =
          (sites.get site).formals.mapM result.wireImage? := by
        rw [siteFormalsExact]
      _ = some (result.siteFormalImages site) :=
        relationSeverSiteFormals_mapM result site
      _ = some step.sourceArguments := congrArg some sourceArgumentsExact.symm
  have contentParametersAccepted :
      content.parameters.mapM result.wireImage? = some parameters := by
    rw [checked.parametersExact, parametersAccepted]
  have boundaryAccepted :
      content.occurrence.boundaryAttachments.mapM result.wireImage? =
        some step.sourceAttachments := by
    calc
      content.occurrence.boundaryAttachments.mapM result.wireImage? =
          (content.formals ++ content.parameters).mapM result.wireImage? :=
        congrArg (fun wires => wires.mapM result.wireImage?)
          checked.boundaryExact
      _ = some (step.sourceArguments ++ step.sourceParameters) := by
        rw [List.mapM_append, formalsAccepted,
          contentParametersAccepted, sourceParametersExact]
        rfl
      _ = some step.sourceAttachments :=
        congrArg some step.sourceAttachmentsExact.symm
  let boundaryEvidence :=
    optionMapM_eq_some_length_get result.wireImage? boundaryAccepted
  let boundaryLength := boundaryEvidence.choose
  have boundaryGet := boundaryEvidence.choose_spec
  have boundaryLanding :
      ∀ position : Fin pattern.val.boundary.length,
        ∃ survives :
            content.occurrence.wireMap
                (pattern.val.boundary.get position) ∈
              ConcreteWireQuantifier.Internal.retainedWires source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires),
          result.wireImage
              (content.occurrence.wireMap
                (pattern.val.boundary.get position)) survives =
            step.sourceAttachments.get
              (Fin.cast step.sourceAttachmentArity.symm position) := by
    intro position
    let sourcePosition :
        Fin content.occurrence.boundaryAttachments.length :=
      Fin.cast content.occurrence.boundaryAttachments_length.symm position
    have transported := boundaryGet sourcePosition
    have sourceGet :
        content.occurrence.boundaryAttachments.get sourcePosition =
          content.occurrence.wireMap
            (pattern.val.boundary.get position) := by
      simp [sourcePosition, Occurrence.boundaryAttachments,
        List.get_eq_getElem]
    have targetPosition :
        Fin.cast boundaryLength sourcePosition =
          Fin.cast step.sourceAttachmentArity.symm position := by
      apply Fin.ext
      rfl
    rw [sourceGet, targetPosition] at transported
    unfold ConcreteWireQuantifier.RelationSeverResult.wireImage? at transported
    split at transported
    · rename_i survives
      exact ⟨by simpa using survives, Option.some.inj transported⟩
    · simp at transported
  exact
    { site := site
      siteExact := siteExact
      applicationExact := applicationExact
      boundarySurvives := fun position => (boundaryLanding position).choose
      sourceAttachmentExact := fun position =>
        (boundaryLanding position).choose_spec.symm }

private theorem InverseStepOccurrenceAlignment.identityRequestsEmpty
    (alignment : InverseStepOccurrenceAlignment result step content) :
    step.attachment.identityRequests = [] := by
  apply step.identityRequests_eq_nil_of_sourceAttachments_coherent
  intro left right same
  rw [alignment.sourceAttachmentExact, alignment.sourceAttachmentExact]
  apply Fin.ext
  simp only [ConcreteWireQuantifier.RelationSeverResult.wireImage_val]
  have mapped := congrArg content.occurrence.wireMap same
  have mappedGetElem := mapped
  simp only [List.get_eq_getElem] at mappedGetElem
  unfold ConcreteWireQuantifier.Internal.retainedWireIndex DenseList.index
  simp [mappedGetElem]

private theorem RelationSeverConcreteReceipt.inverseSteps_sites_length
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.inverse.steps.length =
      (receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site).length := by
  calc
    receipt.inverse.steps.length =
        (receipt.inverse.steps.map
          ConcreteWireQuantifier.RelationJoinStep.application).length := by
      simp
    _ = receipt.result.atoms.length :=
      congrArg List.length receipt.inverseStepsExact
    _ =
        (receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).length := by
      simp [ConcreteWireQuantifier.RelationSeverResult.atoms,
        Data.Finite.allFin_eq_finRange]

private theorem RelationSeverConcreteReceipt.sites_occurrences_length
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    (receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site).length =
      occurrences.length := by
  simpa using congrArg List.length
    receipt.extractions.entries.semanticEvidence_sites

/-- Every retained inverse step is paired, at the same accepted list
position, with the checker-owned original occurrence it restores. -/
private noncomputable def RelationSeverConcreteReceipt.inverseStepAlignment
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (position : Fin receipt.inverse.steps.length) :
    let sites :=
      receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site
    let steps := receipt.inverse.steps
    let stepsSitesLength : steps.length = sites.length :=
      receipt.inverseSteps_sites_length
    let sitesContentsLength : sites.length = occurrences.length :=
      receipt.sites_occurrences_length
    let site := Fin.cast stepsSitesLength position
    let contentPosition :=
      Fin.cast (stepsSitesLength.trans sitesContentsLength) position
    InverseStepOccurrenceAlignment receipt.result (steps.get position)
      (occurrences.get contentPosition) := by
  dsimp only
  let sites :=
    receipt.extractions.semanticEvidence.map
      WireQuantifierSemantics.RelationSeverOccurrence.site
  let steps := receipt.inverse.steps
  have sitesExact : sites = occurrences.map ContentOccurrence.toConcreteSite :=
    receipt.extractions.entries.semanticEvidence_sites
  have stepsSitesLength : steps.length = sites.length :=
    receipt.inverseSteps_sites_length
  have sitesContentsLength : sites.length = occurrences.length :=
    receipt.sites_occurrences_length
  let site : Fin sites.length := Fin.cast stepsSitesLength position
  let contentPosition : Fin occurrences.length :=
    Fin.cast (stepsSitesLength.trans sitesContentsLength) position
  let step := steps.get position
  let content := occurrences.get contentPosition
  have siteExact : sites.get site = content.toConcreteSite := by
    have atPosition := congrArg (fun values => values[site.val]?) sitesExact
    change sites[site.val]? =
      (occurrences.map ContentOccurrence.toConcreteSite)[site.val]?
        at atPosition
    have siteAt : sites[site.val]? = some (sites.get site) := by
      simp [List.getElem?_eq_getElem, site.isLt]
    have indexExact : site.val = contentPosition.val := rfl
    have contentAt : occurrences[site.val]? = some content := by
      rw [indexExact]
      simp [content, List.getElem?_eq_getElem, contentPosition.isLt]
    rw [siteAt, List.getElem?_map, contentAt] at atPosition
    exact Option.some.inj (by simpa using atPosition)
  have applicationExact : step.application = receipt.result.atom site := by
    have applicationsAt := congrArg
      (fun applications => applications[position.val]?)
      receipt.inverseStepsExact
    change
      (steps.map
        ConcreteWireQuantifier.RelationJoinStep.application)[position.val]? =
        receipt.result.atoms[position.val]? at applicationsAt
    have stepAt :
        (steps.map
          ConcreteWireQuantifier.RelationJoinStep.application)[position.val]? =
          some step.application := by
      simp [step, steps, List.getElem?_eq_getElem, position.isLt]
    have positionLtSites : position.val < sites.length := by
      rw [← stepsSitesLength]
      simpa [steps] using position.isLt
    have siteAt :
        (Data.Finite.allFin sites.length)[position.val]? = some site := by
      rw [Data.Finite.allFin_eq_finRange]
      have atPosition :
          (List.finRange sites.length)[position.val]? =
            some ⟨position.val, positionLtSites⟩ := by
        simp [positionLtSites]
      rw [atPosition]
      congr 2
    rw [stepAt] at applicationsAt
    change
      some step.application =
        ((Data.Finite.allFin sites.length).map
          receipt.result.atom)[position.val]? at applicationsAt
    rw [List.getElem?_map, siteAt] at applicationsAt
    exact Option.some.inj applicationsAt
  have stepExact := relationJoinTrace_step_exact
    receipt.inverse.semantic_trace step (List.get_mem steps position)
  have siteArgumentsExact :
      (sites.get site).formals.map
          (fun wire => (source.val.wires wire).sig) =
        receipt.inverse.args := by
    apply Sig.rel.inj
    calc
      .rel ((sites.get site).formals.map
          (fun wire => (source.val.wires wire).sig)) =
          (receipt.result.checked.val.wires
            receipt.result.relationWire).sig := by
        rw [receipt.result.site_formal_signatures site,
          receipt.result.relationWire_signature]
      _ = .rel receipt.inverse.args := receipt.inverse.relation_signature
  have arityExact :
      (sites.get site).formals.length = step.relationArgs.length := by
    calc
      (sites.get site).formals.length =
          ((sites.get site).formals.map
            (fun wire => (source.val.wires wire).sig)).length := by simp
      _ = receipt.inverse.args.length :=
        congrArg List.length siteArgumentsExact
      _ = step.relationArgs.length :=
        congrArg List.length stepExact.1.symm
  exact inverseStepOccurrenceAlignmentOfChecked receipt.result
    receipt.extractions.first content
    (receipt.extractions.entries.get contentPosition)
    receipt.parameters receipt.parametersAccepted step site siteExact
      applicationExact arityExact stepExact.2

/-- No step in an accepted inverse reconstruction can allocate an identity:
its complete boundary vector is the positional sever image of the original
checked occurrence. -/
private theorem RelationSeverConcreteReceipt.inverseStep_identityRequestsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (position : Fin receipt.inverse.steps.length) :
    (receipt.inverse.steps.get position).attachment.identityRequests = [] :=
  (receipt.inverseStepAlignment position).identityRequestsEmpty

/-- Snoc carrier step: transport the existing reconstructed prefix through
atom deletion and splice, then allocate the newly restored occurrence in the
fragment suffix.  The sole separation premise says that no original carrier
already represented by the prefix is the generated atom being consumed. -/
private noncomputable def batchReconstructionSnoc
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    {restored : List (ContentOccurrence source pattern)}
    {current : CheckedDiagram definitions}
    {joinSource : CheckedDiagram definitions}
    (state : BatchReconstructionState sites restored current joinSource)
    (content : ContentOccurrence source pattern)
    {dying : joinSource.val.WireId}
    (step : ConcreteWireQuantifier.RelationJoinStep joinSource dying pattern)
    (priorExact : step.prior = current)
    (priorNodeImageExact :
      HEq step.priorNodeImage state.joinNodeImage)
    (tail : List joinSource.val.NodeId)
    (pendingOriginsExact :
      state.pendingOrigins = step.application :: tail)
    (freshRegionsNew :
      ∀ region, region ≠ pattern.val.diagram.root →
        ¬ BatchCoveredRegion sites restored
          (content.occurrence.regionMap region))
    (freshNodesNew :
      ∀ node, ¬ BatchCoveredNode sites restored
        (content.occurrence.nodeMap node))
    (freshWiresNew :
      ∀ wire, wire ∉ pattern.val.boundary →
        ¬ BatchCoveredWire sites restored
          (content.occurrence.wireMap wire))
    (boundaryRetained :
      ∀ position : Fin pattern.val.boundary.length,
        retainedBySitesWire sites
          (content.occurrence.wireMap
            (pattern.val.boundary.get position)))
    (boundaryWireExact :
      ∀ position : Fin pattern.val.boundary.length,
        step.checkedFragmentWire (pattern.val.boundary.get position) =
          step.checkedPriorWire
            (Fin.cast
              (congrArg
                (fun checked : CheckedDiagram definitions =>
                  checked.val.wireCount) priorExact).symm
              (state.wireImage
                ⟨content.occurrence.wireMap
                    (pattern.val.boundary.get position),
                  Or.inl (boundaryRetained position)⟩)))
    (rootCovered :
      BatchCoveredRegion sites restored
        (content.occurrence.regionMap pattern.val.diagram.root))
    (rootExact :
      step.checkedFragmentRegion pattern.val.diagram.root =
        step.checkedPriorRegion
          (Fin.cast
            (congrArg
              (fun checked : CheckedDiagram definitions =>
                checked.val.regionCount) priorExact).symm
            (state.regionImage
              ⟨content.occurrence.regionMap pattern.val.diagram.root,
                rootCovered⟩))) :
    BatchReconstructionState sites (restored ++ [content]) step.checked
      joinSource := by
  classical
  subst current
  have priorNodeImageExact' :
      step.priorNodeImage = state.joinNodeImage :=
    eq_of_heq priorNodeImageExact
  have currentApplication :
      step.priorApplication ∈ state.pendingApplications := by
    rw [state.pendingApplicationsExact, pendingOriginsExact,
      ← priorNodeImageExact']
    simp only [List.filterMap_cons, step.priorApplicationImage,
      List.mem_cons, true_or]
  have coveredRegion_mono :
      ∀ {region}, BatchCoveredRegion sites restored region →
        BatchCoveredRegion sites (restored ++ [content]) region := by
    intro region covered
    rcases covered with retained | represented
    · exact Or.inl retained
    · rcases represented with
        ⟨candidate, member, patternRegion, nonroot, mapped⟩
      exact Or.inr
        ⟨candidate, List.mem_append.mpr (Or.inl member), patternRegion,
          nonroot, mapped⟩
  exact
    { regionImage := fun region =>
        if old : BatchCoveredRegion sites restored region.1 then
          step.checkedPriorRegion (state.regionImage ⟨region.1, old⟩)
        else
          have fresh := newlyCoveredRegion content region.1 region.2 old
          step.checkedFragmentRegion fresh.choose
      regionImage_injective := by
        intro left right same
        by_cases leftOld : BatchCoveredRegion sites restored left.1
        · by_cases rightOld : BatchCoveredRegion sites restored right.1
          · have priorSame :
                state.regionImage ⟨left.1, leftOld⟩ =
                  state.regionImage ⟨right.1, rightOld⟩ :=
              step.checkedPriorRegion_injective (by
                simpa only [dif_pos leftOld, dif_pos rightOld] using same)
            have coveredSame := state.regionImage_injective priorSame
            apply Subtype.ext
            exact congrArg
              (fun value : { region : source.val.RegionId //
                BatchCoveredRegion sites restored region } => value.1)
              coveredSame
          · let fresh := newlyCoveredRegion content right.1 right.2 rightOld
            exact False.elim
              (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
                fresh.choose fresh.choose_spec.1
                (state.regionImage ⟨left.1, leftOld⟩) (by
                  simpa only [dif_pos leftOld, dif_neg rightOld] using
                    same.symm))
        · by_cases rightOld : BatchCoveredRegion sites restored right.1
          · let fresh := newlyCoveredRegion content left.1 left.2 leftOld
            exact False.elim
              (step.checkedFragmentRegion_ne_checkedPriorRegion_of_nonroot
                fresh.choose fresh.choose_spec.1
                (state.regionImage ⟨right.1, rightOld⟩) (by
                  simpa only [dif_neg leftOld, dif_pos rightOld] using same))
          · let leftFresh :=
                newlyCoveredRegion content left.1 left.2 leftOld
            let rightFresh :=
                newlyCoveredRegion content right.1 right.2 rightOld
            have patternSame : leftFresh.choose = rightFresh.choose :=
              step.checkedFragmentRegion_injective_of_nonroot
                leftFresh.choose_spec.1 rightFresh.choose_spec.1 (by
                  simpa only [dif_neg leftOld, dif_neg rightOld] using same)
            apply Subtype.ext
            exact leftFresh.choose_spec.2.symm.trans
              (patternSame ▸ rightFresh.choose_spec.2)
      retainedRegionImage_val := by
        intro region retained
        split
        next old =>
          rw [step.checkedPriorRegion_val]
          exact state.retainedRegionImage_val region retained
        next old => exact False.elim (old (Or.inl retained))
      regionParentCovered := by
        intro region parent data
        by_cases old : BatchCoveredRegion sites restored region.1
        · exact coveredRegion_mono
            (state.regionParentCovered ⟨region.1, old⟩ parent data)
        · let fresh := newlyCoveredRegion content region.1 region.2 old
          cases patternData : pattern.val.diagram.regions fresh.choose with
          | sheet =>
              have onlyRoot := of_decide_eq_true
                (List.all_eq_true.mp
                  pattern.property.diagram.only_root_is_sheet fresh.choose
                  (Data.Finite.mem_allFin fresh.choose))
              exact False.elim
                (fresh.choose_spec.1 (onlyRoot patternData))
          | cut patternParent =>
              have mappedData := content.occurrence.maps_parentage
                fresh.choose patternParent patternData
              rw [fresh.choose_spec.2] at mappedData
              have parentExact :
                  content.occurrence.regionMap patternParent = parent :=
                CRegion.cut.inj (mappedData.symm.trans data)
              subst parent
              by_cases parentRoot :
                  patternParent = pattern.val.diagram.root
              · subst patternParent
                exact coveredRegion_mono rootCovered
              · exact Or.inr
                  ⟨content, by simp, patternParent, parentRoot, rfl⟩
      regionSheetExact := by
        intro region data
        by_cases old : BatchCoveredRegion sites restored region.1
        · rw [dif_pos old]
          apply step.checkedPriorRegion_sheet
          exact state.regionSheetExact ⟨region.1, old⟩ data
        · let fresh := newlyCoveredRegion content region.1 region.2 old
          cases patternData : pattern.val.diagram.regions fresh.choose with
          | sheet =>
              have onlyRoot := of_decide_eq_true
                (List.all_eq_true.mp
                  pattern.property.diagram.only_root_is_sheet fresh.choose
                  (Data.Finite.mem_allFin fresh.choose))
              exact False.elim
                (fresh.choose_spec.1 (onlyRoot patternData))
          | cut patternParent =>
              have mappedData := content.occurrence.maps_parentage
                fresh.choose patternParent patternData
              rw [fresh.choose_spec.2, data] at mappedData
              contradiction
      regionCutExact := by
        intro region parent data
        by_cases old : BatchCoveredRegion sites restored region.1
        · have parentOld := state.regionParentCovered
            ⟨region.1, old⟩ parent data
          rw [dif_pos old, dif_pos parentOld]
          apply step.checkedPriorRegion_cut
          exact state.regionCutExact ⟨region.1, old⟩ parent data
        · let fresh := newlyCoveredRegion content region.1 region.2 old
          cases patternData : pattern.val.diagram.regions fresh.choose with
          | sheet =>
              have onlyRoot := of_decide_eq_true
                (List.all_eq_true.mp
                  pattern.property.diagram.only_root_is_sheet fresh.choose
                  (Data.Finite.mem_allFin fresh.choose))
              exact False.elim
                (fresh.choose_spec.1 (onlyRoot patternData))
          | cut patternParent =>
              have mappedData := content.occurrence.maps_parentage
                fresh.choose patternParent patternData
              rw [fresh.choose_spec.2] at mappedData
              have parentExact :
                  content.occurrence.regionMap patternParent = parent :=
                CRegion.cut.inj (mappedData.symm.trans data)
              subst parent
              rw [dif_neg old]
              rw [step.checkedFragmentRegion_cut fresh.choose patternParent
                fresh.choose_spec.1 patternData]
              by_cases parentRoot :
                  patternParent = pattern.val.diagram.root
              · subst patternParent
                rw [dif_pos rootCovered]
                exact congrArg CRegion.cut rootExact
              · have parentNew := freshRegionsNew patternParent parentRoot
                rw [dif_neg parentNew]
                let parentFresh := newlyCoveredRegion content
                  (content.occurrence.regionMap patternParent)
                  (Or.inr ⟨content, by simp, patternParent, parentRoot, rfl⟩)
                  parentNew
                have parentPatternExact :
                    parentFresh.choose = patternParent :=
                  content.occurrence.regionMap_injective
                    parentFresh.choose_spec.2
                exact congrArg
                  (fun candidate =>
                    CRegion.cut (step.checkedFragmentRegion candidate))
                  parentPatternExact.symm
      nodeImage := fun node =>
        if old : BatchCoveredNode sites restored node.1 then
          step.checkedPriorNode (state.nodeImage ⟨node.1, old⟩)
            (by
              intro same
              exact state.representedNodesAvoidPending ⟨node.1, old⟩
                (by simpa [same] using currentApplication))
        else
          have fresh := newlyCoveredNode content node.1 node.2 old
          step.checkedFragmentNode fresh.choose
      nodeImage_injective := by
        intro left right same
        by_cases leftOld : BatchCoveredNode sites restored left.1
        · by_cases rightOld : BatchCoveredNode sites restored right.1
          · have leftDifferent :
                state.nodeImage ⟨left.1, leftOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨left.1, leftOld⟩
                (by simpa [exact] using currentApplication)
            have rightDifferent :
                state.nodeImage ⟨right.1, rightOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨right.1, rightOld⟩
                (by simpa [exact] using currentApplication)
            have priorSame := step.checkedPriorNode_injective
              leftDifferent rightDifferent (by
                simpa only [dif_pos leftOld, dif_pos rightOld] using same)
            have coveredSame := state.nodeImage_injective priorSame
            apply Subtype.ext
            exact congrArg
              (fun value : { node : source.val.NodeId //
                BatchCoveredNode sites restored node } => value.1)
              coveredSame
          · let fresh := newlyCoveredNode content right.1 right.2 rightOld
            have leftDifferent :
                state.nodeImage ⟨left.1, leftOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨left.1, leftOld⟩
                (by simpa [exact] using currentApplication)
            exact False.elim
              (step.checkedFragmentNode_ne_checkedPriorNode fresh.choose
                (state.nodeImage ⟨left.1, leftOld⟩) leftDifferent (by
                  simpa only [dif_pos leftOld, dif_neg rightOld] using
                    same.symm))
        · by_cases rightOld : BatchCoveredNode sites restored right.1
          · let fresh := newlyCoveredNode content left.1 left.2 leftOld
            have rightDifferent :
                state.nodeImage ⟨right.1, rightOld⟩ ≠
                  step.priorApplication := by
              intro exact
              exact state.representedNodesAvoidPending ⟨right.1, rightOld⟩
                (by simpa [exact] using currentApplication)
            exact False.elim
              (step.checkedFragmentNode_ne_checkedPriorNode fresh.choose
                (state.nodeImage ⟨right.1, rightOld⟩) rightDifferent (by
                  simpa only [dif_neg leftOld, dif_pos rightOld] using same))
          · let leftFresh := newlyCoveredNode content left.1 left.2 leftOld
            let rightFresh := newlyCoveredNode content right.1 right.2 rightOld
            have patternSame : leftFresh.choose = rightFresh.choose :=
              step.checkedFragmentNode_injective (by
                simpa only [dif_neg leftOld, dif_neg rightOld] using same)
            apply Subtype.ext
            exact leftFresh.choose_spec.symm.trans
              (patternSame ▸ rightFresh.choose_spec)
      nodeRegionCovered := by
        intro node
        by_cases old : BatchCoveredNode sites restored node.1
        · exact coveredRegion_mono
            (state.nodeRegionCovered ⟨node.1, old⟩)
        · let fresh := newlyCoveredNode content node.1 node.2 old
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have sourceRegionExact := congrArg CNode.region sourceData
          simp only [CNode.region_relocate] at sourceRegionExact
          rw [sourceRegionExact]
          by_cases root :
              (pattern.val.diagram.nodes fresh.choose).region =
                pattern.val.diagram.root
          · rw [root]
            exact coveredRegion_mono rootCovered
          · exact Or.inr
              ⟨content, by simp,
                (pattern.val.diagram.nodes fresh.choose).region, root, rfl⟩
      nodeTableExact := by
        intro node
        by_cases old : BatchCoveredNode sites restored node.1
        · have different :
              state.nodeImage ⟨node.1, old⟩ ≠ step.priorApplication := by
            intro same
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (by simpa [same] using currentApplication)
          have transported := step.checkedPriorNode_data
            (state.nodeImage ⟨node.1, old⟩) different
          have priorData := state.nodeTableExact ⟨node.1, old⟩
          rw [priorData] at transported
          have regionOld := state.nodeRegionCovered ⟨node.1, old⟩
          simpa only [dif_pos old, dif_pos regionOld,
            CNode.region_relocate, CNode.relocate_relocate] using transported
        · let fresh := newlyCoveredNode content node.1 node.2 old
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have sourceRegionExact := congrArg CNode.region sourceData
          simp only [CNode.region_relocate] at sourceRegionExact
          have fragmentData := step.checkedFragmentNode_data fresh.choose
          simp only [dif_neg old]
          let allocatedRegion :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } →
                step.checked.val.RegionId := fun region =>
            if prior : BatchCoveredRegion sites restored region.1 then
              step.checkedPriorRegion (state.regionImage ⟨region.1, prior⟩)
            else
              have new := newlyCoveredRegion content region.1 region.2 prior
              step.checkedFragmentRegion new.choose
          have sourceCovered :
              BatchCoveredRegion sites (restored ++ [content])
                (source.val.nodes node.1).region := by
            have newData := content.occurrence.node_data fresh.choose
            rw [fresh.choose_spec] at newData
            have newRegion := congrArg CNode.region newData
            simp only [CNode.region_relocate] at newRegion
            rw [newRegion]
            by_cases atRoot :
                (pattern.val.diagram.nodes fresh.choose).region =
                  pattern.val.diagram.root
            · rw [atRoot]
              exact coveredRegion_mono rootCovered
            · exact Or.inr ⟨content, by simp,
                (pattern.val.diagram.nodes fresh.choose).region,
                atRoot, rfl⟩
          let sourceCarrier :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } :=
            ⟨(source.val.nodes node.1).region, sourceCovered⟩
          change step.checked.val.nodes
              (step.checkedFragmentNode fresh.choose) =
            (source.val.nodes node.1).relocate
              (allocatedRegion sourceCarrier)
          by_cases root :
              (pattern.val.diagram.nodes fresh.choose).region =
                pattern.val.diagram.root
          · have sourceRoot :
                (source.val.nodes node.1).region =
                  content.occurrence.regionMap pattern.val.diagram.root := by
              simpa [root] using sourceRegionExact
            have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap pattern.val.diagram.root,
                      coveredRegion_mono rootCovered⟩ =
                  step.checkedFragmentRegion pattern.val.diagram.root := by
              unfold allocatedRegion
              rw [dif_pos rootCovered]
              exact rootExact.symm
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion pattern.val.diagram.root := by
              exact (congrArg allocatedRegion
                (Subtype.ext sourceRoot)).trans mappedImage
            have relocatedSource := congrArg
              (fun data => data.relocate (allocatedRegion sourceCarrier))
              sourceData
            calc
              step.checked.val.nodes
                    (step.checkedFragmentNode fresh.choose) =
                  (pattern.val.diagram.nodes fresh.choose).relocate
                    (step.checkedFragmentRegion
                      (pattern.val.diagram.nodes fresh.choose).region) :=
                fragmentData
              _ = (pattern.val.diagram.nodes fresh.choose).relocate
                    (step.checkedFragmentRegion pattern.val.diagram.root) := by
                rw [root]
              _ = (pattern.val.diagram.nodes fresh.choose).relocate
                    (allocatedRegion sourceCarrier) :=
                congrArg
                  (fun region =>
                    (pattern.val.diagram.nodes fresh.choose).relocate region)
                  sourceImage.symm
              _ = (source.val.nodes node.1).relocate
                    (allocatedRegion sourceCarrier) := by
                simpa only [CNode.relocate_relocate] using
                  relocatedSource.symm
          · have regionNew := freshRegionsNew
              (pattern.val.diagram.nodes fresh.choose).region root
            let regionFresh := newlyCoveredRegion content
              (content.occurrence.regionMap
                (pattern.val.diagram.nodes fresh.choose).region)
              (Or.inr ⟨content, by simp,
                (pattern.val.diagram.nodes fresh.choose).region, root, rfl⟩)
              regionNew
            have patternRegionExact :
                regionFresh.choose =
                  (pattern.val.diagram.nodes fresh.choose).region :=
              content.occurrence.regionMap_injective
                regionFresh.choose_spec.2
            have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap
                        (pattern.val.diagram.nodes fresh.choose).region,
                      Or.inr ⟨content, by simp,
                        (pattern.val.diagram.nodes fresh.choose).region,
                        root, rfl⟩⟩ =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.nodes fresh.choose).region := by
              unfold allocatedRegion
              rw [dif_neg regionNew]
              exact congrArg step.checkedFragmentRegion patternRegionExact
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.nodes fresh.choose).region := by
              exact (congrArg allocatedRegion
                (Subtype.ext sourceRegionExact)).trans mappedImage
            have relocatedSource := congrArg
              (fun data => data.relocate (allocatedRegion sourceCarrier))
              sourceData
            calc
              step.checked.val.nodes
                    (step.checkedFragmentNode fresh.choose) =
                  (pattern.val.diagram.nodes fresh.choose).relocate
                    (step.checkedFragmentRegion
                      (pattern.val.diagram.nodes fresh.choose).region) :=
                fragmentData
              _ = (pattern.val.diagram.nodes fresh.choose).relocate
                    (allocatedRegion sourceCarrier) :=
                congrArg
                  (fun region =>
                    (pattern.val.diagram.nodes fresh.choose).relocate region)
                  sourceImage.symm
              _ = (source.val.nodes node.1).relocate
                    (allocatedRegion sourceCarrier) := by
                simpa only [CNode.relocate_relocate] using
                  relocatedSource.symm
      portImage := fun node =>
        if old : BatchCoveredNode sites restored node.1 then
          state.portImage ⟨node.1, old⟩
        else
          have fresh := newlyCoveredNode content node.1 node.2 old
          (content.occurrence.portEquivForNode fresh.choose).symm
      portImageCorresponds := by
        intro node port required
        by_cases old : BatchCoveredNode sites restored node.1
        · have different :
              state.nodeImage ⟨node.1, old⟩ ≠ step.priorApplication := by
            intro same
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (by simpa [same] using currentApplication)
          have transported := step.checkedPriorNode_data
            (state.nodeImage ⟨node.1, old⟩) different
          have priorData := state.nodeTableExact ⟨node.1, old⟩
          rw [priorData] at transported
          have priorCorresponds := state.portImageCorresponds
            ⟨node.1, old⟩ port required
          rw [dif_pos old]
          cases sourceData : source.val.nodes node.1 <;>
            simp_all [PortDataCorresponds, CNode.relocate]
        · let fresh := newlyCoveredNode content node.1 node.2 old
          simp only [dif_neg old]
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have fragmentData := step.checkedFragmentNode_data fresh.choose
          change PortDataCorresponds (source.val.nodes node.1)
            (step.checked.val.nodes
              (step.checkedFragmentNode fresh.choose)) port
            ((content.occurrence.portEquivForNode fresh.choose).symm port)
          cases patternData : pattern.val.diagram.nodes fresh.choose with
          | atom region args =>
              have portExact := content.occurrence.portEquivForNode_atom
                fresh.choose region args patternData
              rw [portExact]
              rw [sourceData, fragmentData, patternData]
              exact rfl
          | ref region definition args =>
              have portExact := content.occurrence.portEquivForNode_ref
                fresh.choose region definition args patternData
              rw [portExact]
              rw [sourceData, fragmentData, patternData]
              exact rfl
          | identity region sig arity =>
              have sourceNodeData : source.val.nodes node.1 =
                  .identity (content.occurrence.regionMap region) sig arity := by
                simpa [patternData, CNode.relocate] using sourceData
              have requiredIdentity :
                  port ∈ (List.range arity).map CPort.identity := by
                simpa [ConcreteDiagram.requiredPorts, sourceNodeData] using
                  required
              obtain ⟨index, indexMember, portExact⟩ :=
                List.mem_map.mp requiredIdentity
              have indexLt : index < arity := List.mem_range.mp indexMember
              subst port
              rw [content.occurrence.portEquivForNode_identity fresh.choose
                region sig arity patternData]
              rw [sourceNodeData, fragmentData, patternData]
              refine ⟨rfl, rfl, index,
                ((content.occurrence.identityPortEquiv fresh.choose region sig
                  arity patternData).symm ⟨index, indexLt⟩).1, rfl, ?_⟩
              simp [Occurrence.identityCPortEquiv, indexLt]
      portImageRequired := by
        intro node port
        by_cases old : BatchCoveredNode sites restored node.1
        · have different :
              state.nodeImage ⟨node.1, old⟩ ≠ step.priorApplication := by
            intro same
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (by simpa [same] using currentApplication)
          have transported := step.checkedPriorNode_data
            (state.nodeImage ⟨node.1, old⟩) different
          have priorData := state.nodeTableExact ⟨node.1, old⟩
          have priorRequired := state.portImageRequired ⟨node.1, old⟩ port
          simp only [dif_pos old]
          rw [priorData] at transported
          rw [priorData] at priorRequired
          rw [transported]
          simpa using priorRequired
        · let fresh := newlyCoveredNode content node.1 node.2 old
          simp only [dif_neg old]
          have sourceData := content.occurrence.node_data fresh.choose
          rw [fresh.choose_spec] at sourceData
          have fragmentData := step.checkedFragmentNode_data fresh.choose
          cases patternData : pattern.val.diagram.nodes fresh.choose with
          | atom region args =>
              rw [content.occurrence.portEquivForNode_atom fresh.choose
                region args patternData]
              rw [sourceData, fragmentData, patternData]
              rfl
          | ref region definition args =>
              rw [content.occurrence.portEquivForNode_ref fresh.choose
                region definition args patternData]
              rw [sourceData, fragmentData, patternData]
              rfl
          | identity region sig arity =>
              rw [content.occurrence.portEquivForNode_identity fresh.choose
                region sig arity patternData]
              rw [sourceData, fragmentData, patternData]
              cases port with
              | head => simp [requiredPortsForNode, CNode.relocate, CNode.region,
                  Occurrence.identityCPortEquiv]
              | arg index => simp [requiredPortsForNode, CNode.relocate, CNode.region,
                  Occurrence.identityCPortEquiv]
              | identity index =>
                  by_cases indexLt : index < arity
                  · simp [requiredPortsForNode, CNode.relocate, CNode.region,
                      Occurrence.identityCPortEquiv, indexLt]
                  · simp [requiredPortsForNode, CNode.relocate, CNode.region,
                      Occurrence.identityCPortEquiv, indexLt]
      wireImage := fun wire =>
        if old : BatchCoveredWire sites restored wire.1 then
          step.checkedPriorWire (state.wireImage ⟨wire.1, old⟩)
        else
          have fresh := newlyCoveredWire content wire.1 wire.2 old
          step.checkedFragmentWire fresh.choose
      wireImage_injective := by
        intro left right same
        by_cases leftOld : BatchCoveredWire sites restored left.1
        · by_cases rightOld : BatchCoveredWire sites restored right.1
          · have priorSame :
                state.wireImage ⟨left.1, leftOld⟩ =
                  state.wireImage ⟨right.1, rightOld⟩ :=
              step.checkedPriorWire_injective (by
                simpa only [dif_pos leftOld, dif_pos rightOld] using same)
            have coveredSame := state.wireImage_injective priorSame
            apply Subtype.ext
            exact congrArg
              (fun value : { wire : source.val.WireId //
                BatchCoveredWire sites restored wire } => value.1)
              coveredSame
          · let fresh := newlyCoveredWire content right.1 right.2 rightOld
            exact False.elim
              (step.checkedFragmentWire_ne_checkedPriorWire_of_internal
                fresh.choose fresh.choose_spec.1
                (state.wireImage ⟨left.1, leftOld⟩) (by
                  simpa only [dif_pos leftOld, dif_neg rightOld] using
                    same.symm))
        · by_cases rightOld : BatchCoveredWire sites restored right.1
          · let fresh := newlyCoveredWire content left.1 left.2 leftOld
            exact False.elim
              (step.checkedFragmentWire_ne_checkedPriorWire_of_internal
                fresh.choose fresh.choose_spec.1
                (state.wireImage ⟨right.1, rightOld⟩) (by
                  simpa only [dif_neg leftOld, dif_pos rightOld] using same))
          · let leftFresh := newlyCoveredWire content left.1 left.2 leftOld
            let rightFresh := newlyCoveredWire content right.1 right.2 rightOld
            have patternSame : leftFresh.choose = rightFresh.choose :=
              step.checkedFragmentWire_injective_of_internal
                leftFresh.choose_spec.1 rightFresh.choose_spec.1 (by
                  simpa only [dif_neg leftOld, dif_neg rightOld] using same)
            apply Subtype.ext
            exact leftFresh.choose_spec.2.symm.trans
              (patternSame ▸ rightFresh.choose_spec.2)
      retainedWireImage_val := by
        intro wire retained
        have old : BatchCoveredWire sites restored wire := Or.inl retained
        rw [dif_pos old, step.checkedPriorWire_val]
        exact state.retainedWireImage_val wire retained
      wireScopeCovered := by
        intro wire
        by_cases old : BatchCoveredWire sites restored wire.1
        · exact coveredRegion_mono
            (state.wireScopeCovered ⟨wire.1, old⟩)
        · let fresh := newlyCoveredWire content wire.1 wire.2 old
          have scopeExact := content.occurrence.internalWire_scope
            fresh.choose fresh.choose_spec.1
          rw [fresh.choose_spec.2] at scopeExact
          rw [scopeExact]
          by_cases root :
              (pattern.val.diagram.wires fresh.choose).scope =
                pattern.val.diagram.root
          · rw [root]
            exact coveredRegion_mono rootCovered
          · exact Or.inr ⟨content, by simp,
              (pattern.val.diagram.wires fresh.choose).scope, root, rfl⟩
      wireSignatureExact := by
        intro wire
        by_cases old : BatchCoveredWire sites restored wire.1
        · rw [dif_pos old]
          calc
            (step.checked.val.wires
                (step.checkedPriorWire
                  (state.wireImage ⟨wire.1, old⟩))).sig =
                (step.prior.val.wires
                  (state.wireImage ⟨wire.1, old⟩)).sig :=
              step.checkedPriorWire_signature _
            _ = (source.val.wires wire.1).sig :=
              state.wireSignatureExact ⟨wire.1, old⟩
        · rw [dif_neg old]
          let fresh := newlyCoveredWire content wire.1 wire.2 old
          have sourceSignature := content.occurrence.wire_signature_preserved
            fresh.choose
          rw [fresh.choose_spec.2] at sourceSignature
          exact (step.checkedFragmentWire_signature_of_internal fresh.choose
            fresh.choose_spec.1).trans sourceSignature.symm
      wireScopeExact := by
        intro wire
        by_cases old : BatchCoveredWire sites restored wire.1
        · have transported := step.checkedPriorWire_scope
            (state.wireImage ⟨wire.1, old⟩)
          rw [state.wireScopeExact ⟨wire.1, old⟩] at transported
          have scopeOld := state.wireScopeCovered ⟨wire.1, old⟩
          simpa only [dif_pos old, dif_pos scopeOld] using transported
        · let fresh := newlyCoveredWire content wire.1 wire.2 old
          have sourceScope := content.occurrence.internalWire_scope
            fresh.choose fresh.choose_spec.1
          rw [fresh.choose_spec.2] at sourceScope
          have fragmentScope := step.checkedFragmentWire_scope_of_internal
            fresh.choose fresh.choose_spec.1
          rw [dif_neg old]
          let allocatedRegion :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } →
                step.checked.val.RegionId := fun region =>
            if prior : BatchCoveredRegion sites restored region.1 then
              step.checkedPriorRegion (state.regionImage ⟨region.1, prior⟩)
            else
              have new := newlyCoveredRegion content region.1 region.2 prior
              step.checkedFragmentRegion new.choose
          have sourceCovered :
              BatchCoveredRegion sites (restored ++ [content])
                (source.val.wires wire.1).scope := by
            rw [sourceScope]
            by_cases atRoot :
                (pattern.val.diagram.wires fresh.choose).scope =
                  pattern.val.diagram.root
            · rw [atRoot]
              exact coveredRegion_mono rootCovered
            · exact Or.inr ⟨content, by simp,
                (pattern.val.diagram.wires fresh.choose).scope,
                atRoot, rfl⟩
          let sourceCarrier :
              { region : source.val.RegionId //
                BatchCoveredRegion sites (restored ++ [content]) region } :=
            ⟨(source.val.wires wire.1).scope, sourceCovered⟩
          change
            (step.checked.val.wires
              (step.checkedFragmentWire fresh.choose)).scope =
                allocatedRegion sourceCarrier
          by_cases root :
              (pattern.val.diagram.wires fresh.choose).scope =
                pattern.val.diagram.root
          · have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap pattern.val.diagram.root,
                      coveredRegion_mono rootCovered⟩ =
                  step.checkedFragmentRegion pattern.val.diagram.root := by
              unfold allocatedRegion
              rw [dif_pos rootCovered]
              exact rootExact.symm
            have sourceRoot :
                (source.val.wires wire.1).scope =
                  content.occurrence.regionMap pattern.val.diagram.root := by
              simpa [root] using sourceScope
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion pattern.val.diagram.root :=
              (congrArg allocatedRegion
                (Subtype.ext sourceRoot)).trans mappedImage
            rw [fragmentScope, root]
            exact sourceImage.symm
          · have regionNew := freshRegionsNew
              (pattern.val.diagram.wires fresh.choose).scope root
            let regionFresh := newlyCoveredRegion content
              (content.occurrence.regionMap
                (pattern.val.diagram.wires fresh.choose).scope)
              (Or.inr ⟨content, by simp,
                (pattern.val.diagram.wires fresh.choose).scope, root, rfl⟩)
              regionNew
            have patternRegionExact : regionFresh.choose =
                (pattern.val.diagram.wires fresh.choose).scope :=
              content.occurrence.regionMap_injective
                regionFresh.choose_spec.2
            have mappedImage :
                allocatedRegion
                    ⟨content.occurrence.regionMap
                        (pattern.val.diagram.wires fresh.choose).scope,
                      Or.inr ⟨content, by simp,
                        (pattern.val.diagram.wires fresh.choose).scope,
                        root, rfl⟩⟩ =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.wires fresh.choose).scope := by
              unfold allocatedRegion
              rw [dif_neg regionNew]
              exact congrArg step.checkedFragmentRegion patternRegionExact
            have sourceImage :
                allocatedRegion sourceCarrier =
                  step.checkedFragmentRegion
                    (pattern.val.diagram.wires fresh.choose).scope :=
              (congrArg allocatedRegion
                (Subtype.ext sourceScope)).trans mappedImage
            exact fragmentScope.trans sourceImage.symm
      wireEndpointForward := by
        intro wire endpoint incident nodeCovered
        by_cases wireOld : BatchCoveredWire sites restored wire.1
        · by_cases nodeOld : BatchCoveredNode sites restored endpoint.node
          · let priorEndpoint : CEndpoint step.prior.val.nodeCount :=
              { node := state.nodeImage ⟨endpoint.node, nodeOld⟩
                port := state.portImage ⟨endpoint.node, nodeOld⟩ endpoint.port }
            have priorIncident := state.wireEndpointForward
              ⟨wire.1, wireOld⟩ endpoint incident nodeOld
            have different : priorEndpoint.node ≠ step.priorApplication := by
              intro same
              exact state.representedNodesAvoidPending ⟨endpoint.node, nodeOld⟩
                (by
                  have imageExact :
                      state.nodeImage ⟨endpoint.node, nodeOld⟩ =
                        step.priorApplication := by
                    simpa [priorEndpoint] using same
                  rw [imageExact]
                  exact currentApplication)
            have transported := step.checkedPriorEndpoint_mem
              (state.wireImage ⟨wire.1, wireOld⟩) priorEndpoint different
              priorIncident
            simpa only [dif_pos wireOld, dif_pos nodeOld,
              ConcreteWireQuantifier.RelationJoinStep.checkedPriorEndpoint,
              priorEndpoint] using transported
          · let freshNode := newlyCoveredNode content endpoint.node
              nodeCovered nodeOld
            rcases Reconstruction.occurrenceEndpointMap_preimage
                content.occurrence
                freshNode.choose wire.1 endpoint incident
                freshNode.choose_spec with
              ⟨patternWire, patternEndpoint, patternIncident,
                mappedWire, endpointExact⟩
            have patternNodeExact : patternEndpoint.node = freshNode.choose := by
              apply content.occurrence.nodeMap_injective
              exact (congrArg CEndpoint.node endpointExact).trans
                freshNode.choose_spec.symm
            have boundary : patternWire ∈ pattern.val.boundary :=
              Classical.byContradiction (fun internal =>
                (freshWiresNew patternWire internal)
                  (mappedWire ▸ wireOld))
            obtain ⟨position, positionExact⟩ := List.get_of_mem boundary
            have imageWireExact :
                step.checkedFragmentWire patternWire =
                  step.checkedPriorWire
                    (state.wireImage ⟨wire.1, wireOld⟩) := by
              subst patternWire
              rw [boundaryWireExact position]
              have carriers :
                  (⟨content.occurrence.wireMap
                      (pattern.val.boundary.get position),
                    Or.inl (boundaryRetained position)⟩ :
                    { sourceWire : source.val.WireId //
                      BatchCoveredWire sites restored sourceWire }) =
                    ⟨wire.1, wireOld⟩ := by
                apply Subtype.ext
                exact mappedWire
              apply congrArg step.checkedPriorWire
              apply Fin.ext
              simpa using congrArg Fin.val (congrArg state.wireImage carriers)
            have mappedIncident := step.checkedFragmentEndpoint_mem
              patternWire patternEndpoint patternIncident
            rw [imageWireExact] at mappedIncident
            have inversePortExact :
                (content.occurrence.portEquivForNode freshNode.choose).symm
                    endpoint.port = patternEndpoint.port := by
              rw [← congrArg CEndpoint.port endpointExact,
                ← patternNodeExact]
              exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
            simpa only [dif_pos wireOld, dif_neg nodeOld,
              ConcreteWireQuantifier.RelationJoinStep.checkedFragmentEndpoint,
              Occurrence.endpointMapForNode, patternNodeExact,
              inversePortExact] using mappedIncident
        · let freshWire := newlyCoveredWire content wire.1 wire.2 wireOld
          by_cases nodeOld : BatchCoveredNode sites restored endpoint.node
          · have internalIncident : endpoint ∈
                (source.val.wires
                  (content.occurrence.wireMap freshWire.choose)).endpoints := by
              simpa [freshWire.choose_spec.2] using incident
            rcases Reconstruction.occurrenceInternalEndpoint_node_preimage
                content.occurrence
                freshWire.choose freshWire.choose_spec.1 endpoint
                internalIncident with
              ⟨patternEndpoint, _patternIncident, mappedNode⟩
            exact False.elim
              ((freshNodesNew patternEndpoint.node)
                (mappedNode ▸ nodeOld))
          · let freshNode := newlyCoveredNode content endpoint.node
              nodeCovered nodeOld
            rcases Reconstruction.occurrenceEndpointMap_preimage
                content.occurrence
                freshNode.choose wire.1 endpoint incident
                freshNode.choose_spec with
              ⟨patternWire, patternEndpoint, patternIncident,
                mappedWire, endpointExact⟩
            have patternInternal : patternWire ∉ pattern.val.boundary := by
              intro boundary
              exact content.occurrence.internalBoundary_disjoint
                freshWire.choose patternWire freshWire.choose_spec.1 boundary
                (freshWire.choose_spec.2.trans mappedWire.symm)
            have patternWireExact : patternWire = freshWire.choose :=
              content.occurrence.internalWire_injective
                patternWire freshWire.choose patternInternal
                freshWire.choose_spec.1
                (mappedWire.trans freshWire.choose_spec.2.symm)
            have patternNodeExact : patternEndpoint.node = freshNode.choose := by
              apply content.occurrence.nodeMap_injective
              exact (congrArg CEndpoint.node endpointExact).trans
                freshNode.choose_spec.symm
            have mappedIncident := step.checkedFragmentEndpoint_mem
              patternWire patternEndpoint patternIncident
            have inversePortExact :
                (content.occurrence.portEquivForNode freshNode.choose).symm
                    endpoint.port = patternEndpoint.port := by
              rw [← congrArg CEndpoint.port endpointExact,
                ← patternNodeExact]
              exact Data.Finite.FiniteEquiv.symm_apply_apply _ _
            simpa only [dif_neg wireOld, dif_neg nodeOld, patternWireExact,
              ConcreteWireQuantifier.RelationJoinStep.checkedFragmentEndpoint,
              Occurrence.endpointMapForNode, patternNodeExact,
              inversePortExact] using mappedIncident
      joinNodeImage := step.checkedNodeImage
      pendingOrigins := tail
      pendingApplications :=
        step.checkedRemainingNodes state.pendingApplications
      pendingApplicationsExact := by
        rw [state.pendingApplicationsExact, pendingOriginsExact,
          ← priorNodeImageExact', List.filterMap_cons,
          step.priorApplicationImage]
        change
          step.checkedRemainingNodes
              (step.priorApplication ::
                tail.filterMap step.priorNodeImage) =
            tail.filterMap step.checkedNodeImage
        rw [show
          step.checkedRemainingNodes
              (step.priorApplication ::
                tail.filterMap step.priorNodeImage) =
            step.checkedRemainingNodes
              (tail.filterMap step.priorNodeImage) by
          simp [ConcreteWireQuantifier.RelationJoinStep.checkedRemainingNodes]]
        exact
          (step.checkedNodeImages_eq_checkedRemainingNodes tail).symm
      representedNodesAvoidPending := by
        intro node pending
        unfold ConcreteWireQuantifier.RelationJoinStep.checkedRemainingNodes at pending
        rw [List.mem_filterMap] at pending
        rcases pending with ⟨prior, priorMember, emitted⟩
        split at emitted
        · rename_i priorDifferent
          have mapped := Option.some.inj emitted
          by_cases old : BatchCoveredNode sites restored node.1
          · have representedDifferent :
                state.nodeImage ⟨node.1, old⟩ ≠
                  step.priorApplication := by
              intro representedExact
              exact state.representedNodesAvoidPending ⟨node.1, old⟩
                (by simpa [representedExact] using currentApplication)
            have priorExact : state.nodeImage ⟨node.1, old⟩ = prior :=
              have mappedOld :
                  step.checkedPriorNode prior priorDifferent =
                    step.checkedPriorNode
                      (state.nodeImage ⟨node.1, old⟩)
                      representedDifferent := by
                simpa only [dif_pos old] using mapped
              step.checkedPriorNode_injective representedDifferent
                priorDifferent mappedOld.symm
            exact state.representedNodesAvoidPending ⟨node.1, old⟩
              (priorExact.symm ▸ priorMember)
          · have fresh : ∃ patternNode,
                content.occurrence.nodeMap patternNode = node.1 := by
              rcases node.2 with retained | restoredAll
              · exact False.elim (old (Or.inl retained))
              · rcases restoredAll with
                  ⟨candidate, member, patternNode, occurrenceExact⟩
                rcases List.mem_append.mp member with previous | final
                · exact False.elim
                    (old (Or.inr
                      ⟨candidate, previous, patternNode,
                        occurrenceExact⟩))
                · have candidateExact : candidate = content := by
                    simpa using final
                  subst candidate
                  exact ⟨patternNode, occurrenceExact⟩
            have mappedFresh :
                step.checkedPriorNode prior priorDifferent =
                  step.checkedFragmentNode fresh.choose := by
              simpa only [dif_neg old] using mapped
            exact step.checkedFragmentNode_ne_checkedPriorNode
              fresh.choose prior priorDifferent mappedFresh.symm
        · contradiction }

/-- The reconstruction fold owns both the partial carrier state and the exact
unconsumed suffix of sever-generated relation atoms. -/
private structure BatchReconstructionTraceState
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (contents : List (ContentOccurrence source pattern))
    {steps : List (ConcreteWireQuantifier.RelationJoinStep
      result.checked result.relationWire pattern)}
    (current : CheckedDiagram definitions)
    (nodeImage : result.checked.val.NodeId → Option current.val.NodeId)
    (currentDying : current.val.WireId) where
  state : BatchReconstructionState sites contents current result.checked
  pendingOriginsExact :
    state.pendingOrigins = result.atoms.drop steps.length
  joinNodeImageExact : HEq state.joinNodeImage nodeImage
  representedWiresAvoidDying :
    ∀ wire, state.wireImage wire ≠ currentDying

private theorem relationJoinTrace_wireImage_val
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      source dying pattern parameters args steps final regionImage nodeImage
        wireImage finalDying finalScope) :
    ∀ wire, (wireImage wire).val = wire.val := by
  induction trace with
  | nil => intro wire; rfl
  | snoc trace step priorExact priorRegionExact priorNodeExact priorWireExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      induction =>
      cases priorExact
      intro wire
      rw [step.checkedWireImageExact, step.baseWireImageExact]
      change (step.priorWireImage wire).val = wire.val
      have imagesExact := eq_of_heq priorWireExact
      rw [imagesExact]
      exact induction wire

/-- Structural fold of the accepted inverse trace.  Its only list premises
state that the restored occurrence prefix and consumed application prefix
have the same length and order as the trace itself. -/
private theorem batchReconstructionTraceFold_exists
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (allContents : List (ContentOccurrence source pattern))
    (first : ContentOccurrence source pattern)
    (entries : CheckedOccurrenceList scope first allContents)
    (sitesExact : sites = allContents.map ContentOccurrence.toConcreteSite)
    (parameters : List result.checked.val.WireId)
    (parametersAccepted : first.parameters.mapM result.wireImage? =
      some parameters)
    (args : List Sig)
    (relationSignature :
      (result.checked.val.wires result.relationWire).sig = .rel args)
    {steps : List (ConcreteWireQuantifier.RelationJoinStep
      result.checked result.relationWire pattern)}
    {current : CheckedDiagram definitions}
    {regionImage : result.checked.val.RegionId → current.val.RegionId}
    {nodeImage : result.checked.val.NodeId → Option current.val.NodeId}
    {wireImage : result.checked.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId}
    {currentScope : current.val.RegionId}
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      result.checked result.relationWire pattern parameters args steps current
        regionImage nodeImage wireImage currentDying currentScope)
    (contents : List (ContentOccurrence source pattern))
    (suffix : List (ContentOccurrence source pattern))
    (allContentsDecomposition : allContents = contents ++ suffix)
    (contentsLength : contents.length = steps.length)
    (applicationsExact :
      steps.map ConcreteWireQuantifier.RelationJoinStep.application =
        result.atoms.take steps.length) :
    Nonempty
      (BatchReconstructionTraceState (steps := steps) result contents current
        nodeImage currentDying) := by
  induction trace generalizing contents suffix with
  | nil =>
      have contentsEmpty : contents = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using contentsLength)
      subst contents
      exact ⟨
        { state := batchReconstructionNil result
          pendingOriginsExact := by simp [batchReconstructionNil]
          joinNodeImageExact := by rfl
          representedWiresAvoidDying := by
            intro wire same
            have values := congrArg Fin.val same
            simp [batchReconstructionNil] at values
            have bound :=
              (ConcreteWireQuantifier.Internal.retainedWireIndex source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires)
                wire.1 (by
                  exact (result.retainedWire_iff wire.1).mpr (by
                    simpa [BatchCoveredWire, restoredWire,
                      retainedBySitesWire] using wire.2))).isLt
            omega }⟩
  | @snoc priorSteps priorCurrent priorRegionImage priorNodeImage
      priorWireImage priorDying priorScope trace step priorExact
      priorRegionExact priorNodeExact priorWireExact priorDyingExact
      priorScopeExact relationArgsExact sourceParametersExact induction =>
      cases priorExact
      have contentsNonempty : contents ≠ [] := by
        intro contentsEmpty
        subst contents
        simp at contentsLength
      let prefixContents := contents.dropLast
      let content := contents.getLast contentsNonempty
      have contentsDecomposition : prefixContents ++ [content] = contents := by
        exact List.dropLast_concat_getLast contentsNonempty
      have prefixLength : prefixContents.length = priorSteps.length := by
        have finalLength : contents.length = priorSteps.length + 1 := by
          simpa using contentsLength
        simp [prefixContents, finalLength]
      have prefixApplicationsExact :
          priorSteps.map
              ConcreteWireQuantifier.RelationJoinStep.application =
            result.atoms.take priorSteps.length := by
        have restricted := congrArg (List.take priorSteps.length)
          applicationsExact
        simpa [List.map_append, List.take_take,
          Nat.min_eq_left (Nat.le_succ priorSteps.length)] using restricted
      obtain ⟨priorState⟩ :=
        induction prefixContents (content :: suffix) (by
          calc
            allContents = contents ++ suffix := allContentsDecomposition
            _ = (prefixContents ++ [content]) ++ suffix := by
              rw [contentsDecomposition]
            _ = prefixContents ++ content :: suffix := by simp)
          prefixLength prefixApplicationsExact
      have atomsDecomposition :
          result.atoms =
            (priorSteps.map
                ConcreteWireQuantifier.RelationJoinStep.application ++
              [step.application]) ++
              result.atoms.drop (priorSteps.length + 1) := by
        calc
          result.atoms =
              result.atoms.take (priorSteps.length + 1) ++
                result.atoms.drop (priorSteps.length + 1) := by
            exact (List.take_append_drop (priorSteps.length + 1)
              result.atoms).symm
          _ =
              (priorSteps.map
                  ConcreteWireQuantifier.RelationJoinStep.application ++
                [step.application]) ++
                result.atoms.drop (priorSteps.length + 1) := by
            have fullApplications :
                priorSteps.map
                    ConcreteWireQuantifier.RelationJoinStep.application ++
                  [step.application] =
                result.atoms.take (priorSteps.length + 1) := by
              simpa [List.map_append] using applicationsExact
            rw [← fullApplications]
      have pendingHead :
          result.atoms.drop priorSteps.length =
            step.application ::
              result.atoms.drop (priorSteps.length + 1) := by
        calc
          result.atoms.drop priorSteps.length =
              ((priorSteps.map
                    ConcreteWireQuantifier.RelationJoinStep.application ++
                  [step.application]) ++
                result.atoms.drop (priorSteps.length + 1)).drop
                  priorSteps.length :=
            congrArg (List.drop priorSteps.length) atomsDecomposition
          _ = step.application ::
              result.atoms.drop (priorSteps.length + 1) := by simp
      have priorNodeStateExact :
          HEq step.priorNodeImage priorState.state.joinNodeImage :=
        priorNodeExact.trans priorState.joinNodeImageExact.symm
      have currentAllDecomposition :
          allContents = prefixContents ++ content :: suffix := by
        calc
          allContents = contents ++ suffix := allContentsDecomposition
          _ = (prefixContents ++ [content]) ++ suffix := by
            rw [contentsDecomposition]
          _ = prefixContents ++ content :: suffix := by simp
      have freshRegionsNew :
          ∀ region, region ≠ pattern.val.diagram.root →
            ¬ BatchCoveredRegion sites prefixContents
              (content.occurrence.regionMap region) :=
        properRegion_not_covered_before result entries sitesExact content
          suffix currentAllDecomposition
      have freshNodesNew :
          ∀ node, ¬ BatchCoveredNode sites prefixContents
            (content.occurrence.nodeMap node) :=
        nodeImage_not_covered_before result entries sitesExact content suffix
          currentAllDecomposition
      have freshWiresNew :
          ∀ wire, wire ∉ pattern.val.boundary →
            ¬ BatchCoveredWire sites prefixContents
              (content.occurrence.wireMap wire) :=
        internalWireImage_not_covered_before result entries sitesExact content
          suffix currentAllDecomposition
      have contentMember : content ∈ allContents := by
        rw [currentAllDecomposition]
        simp
      have positionLtSites : priorSteps.length < sites.length := by
        have lengths := congrArg List.length sitesExact
        rw [currentAllDecomposition] at lengths
        simp at lengths
        omega
      let site : Fin sites.length :=
        ⟨priorSteps.length, positionLtSites⟩
      have siteExact : sites.get site = content.toConcreteSite := by
        have atPosition := congrArg
          (fun candidates => candidates[priorSteps.length]?) sitesExact
        rw [currentAllDecomposition] at atPosition
        change sites[priorSteps.length]? =
          ((prefixContents ++ content :: suffix).map
            ContentOccurrence.toConcreteSite)[priorSteps.length]?
            at atPosition
        have leftAt : sites[priorSteps.length]? = some (sites.get site) := by
          simp [List.getElem?_eq_getElem, positionLtSites, site]
        have rightAt :
            ((prefixContents ++ content :: suffix).map
              ContentOccurrence.toConcreteSite)[priorSteps.length]? =
              some content.toConcreteSite := by
          simp [prefixLength]
        rw [leftAt, rightAt] at atPosition
        exact Option.some.inj atPosition
      have applicationExact : step.application = result.atom site := by
        have atPosition := congrArg
          (fun applications => applications[priorSteps.length]?)
          applicationsExact
        simpa [List.map_append, site,
          ConcreteWireQuantifier.RelationSeverResult.atoms,
          Data.Finite.allFin_eq_finRange, positionLtSites] using atPosition
      obtain ⟨contentPosition, contentPositionExact⟩ :=
        List.get_of_mem contentMember
      let checkedContent : CheckedOccurrence scope first content :=
        contentPositionExact ▸ entries.get contentPosition
      have siteArgumentsExact :
          (sites.get site).formals.map
              (fun wire => (source.val.wires wire).sig) = args := by
        apply Sig.rel.inj
        calc
          .rel ((sites.get site).formals.map
              (fun wire => (source.val.wires wire).sig)) =
              (result.checked.val.wires result.relationWire).sig := by
            rw [result.site_formal_signatures site,
              result.relationWire_signature]
          _ = .rel args := relationSignature
      have arityExact :
          (sites.get site).formals.length = step.relationArgs.length := by
        calc
          (sites.get site).formals.length =
              ((sites.get site).formals.map
                (fun wire => (source.val.wires wire).sig)).length := by simp
          _ = args.length := congrArg List.length siteArgumentsExact
          _ = step.relationArgs.length :=
            congrArg List.length relationArgsExact.symm
      let alignment := inverseStepOccurrenceAlignmentOfChecked result first
        content checkedContent parameters parametersAccepted step site
        siteExact applicationExact arityExact sourceParametersExact
      have priorWireVal :
          ∀ wire, (step.priorWireImage wire).val = wire.val := by
        intro wire
        have imagesExact := eq_of_heq priorWireExact
        rw [imagesExact]
        exact relationJoinTrace_wireImage_val trace wire
      have boundaryRetained :
          ∀ position : Fin pattern.val.boundary.length,
            retainedBySitesWire sites
              (content.occurrence.wireMap
                (pattern.val.boundary.get position)) := by
        intro position
        exact (result.retainedWire_iff _).mp
          (alignment.boundarySurvives position)
      have boundaryWireExact :
          ∀ position : Fin pattern.val.boundary.length,
            step.checkedFragmentWire (pattern.val.boundary.get position) =
              step.checkedPriorWire
                (priorState.state.wireImage
                  ⟨content.occurrence.wireMap
                      (pattern.val.boundary.get position),
                    Or.inl (boundaryRetained position)⟩) := by
        intro position
        apply Fin.ext
        let representative := DenseList.index pattern.val.boundary
          (pattern.val.boundary.get position)
            (List.get_mem pattern.val.boundary position)
        have representativeGet :
            pattern.val.boundary.get representative =
              pattern.val.boundary.get position :=
          DenseList.get_index _ _ _
        have attachmentAt := alignment.sourceAttachmentExact representative
        let originalWire := content.occurrence.wireMap
          (pattern.val.boundary.get position)
        have originalSurvives : originalWire ∈
            ConcreteWireQuantifier.Internal.retainedWires source
              (sites.flatMap
                ConcreteWireQuantifier.RelationSeverSite.removedWires) := by
          unfold originalWire
          rw [← representativeGet]
          exact alignment.boundarySurvives representative
        have attachmentVal :
            (step.sourceAttachments.get
              (Fin.cast step.sourceAttachmentArity.symm representative)).val =
              (ConcreteWireQuantifier.Internal.retainedWireIndex source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires)
                originalWire originalSurvives).val := by
          calc
            (step.sourceAttachments.get
                (Fin.cast step.sourceAttachmentArity.symm representative)).val =
                (result.wireImage
                  (content.occurrence.wireMap
                    (pattern.val.boundary.get representative))
                  (alignment.boundarySurvives representative)).val :=
              congrArg Fin.val attachmentAt
            _ = (ConcreteWireQuantifier.Internal.retainedWireIndex source
                  (sites.flatMap
                    ConcreteWireQuantifier.RelationSeverSite.removedWires)
                  (content.occurrence.wireMap
                    (pattern.val.boundary.get representative))
                  (alignment.boundarySurvives representative)).val :=
              result.wireImage_val _ _
            _ = (ConcreteWireQuantifier.Internal.retainedWireIndex source
                  (sites.flatMap
                    ConcreteWireQuantifier.RelationSeverSite.removedWires)
                  originalWire
                  originalSurvives).val := by
              congr 2
              exact congrArg content.occurrence.wireMap representativeGet
        calc
          (step.checkedFragmentWire
              (pattern.val.boundary.get position)).val =
              (step.sourceAttachments.get
                (Fin.cast step.sourceAttachmentArity.symm representative)).val := by
            simp [ConcreteWireQuantifier.RelationJoinStep.checkedFragmentWire,
              ConcreteSpliceAttachment.fragmentWire,
              ConcreteSpliceAttachment.representativeTarget,
              ConcreteSpliceAttachment.representativePosition,
              representative, step.targetExact]
            rw [step.baseWireImageExact]
            exact priorWireVal _
          _ = (ConcreteWireQuantifier.Internal.retainedWireIndex source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires)
                originalWire
                originalSurvives).val :=
            attachmentVal
          _ = (priorState.state.wireImage
                ⟨originalWire, Or.inl (boundaryRetained position)⟩).val := by
            symm
            exact priorState.state.retainedWireImage_val originalWire
              (boundaryRetained position)
          _ = (step.checkedPriorWire
                (priorState.state.wireImage
                  ⟨originalWire, Or.inl (boundaryRetained position)⟩)).val := by
            rw [step.checkedPriorWire_val]
      have rootRetainedMember :
          content.occurrence.regionMap pattern.val.diagram.root ∈
            ConcreteWireQuantifier.Internal.retainedRegions source
              (sites.flatMap
                ConcreteWireQuantifier.RelationSeverSite.removedRegions) := by
        have retained := result.siteRegion_survives site
        rw [siteExact] at retained
        have regionExact :=
          entries.occurrenceRegion_eq_selectionRegion content contentMember
        simpa [Occurrence.maps_root, regionExact] using retained
      have rootRetained :
          retainedBySitesRegion sites
            (content.occurrence.regionMap pattern.val.diagram.root) :=
        (result.retainedRegion_iff _).mp rootRetainedMember
      have rootCovered :
          BatchCoveredRegion sites prefixContents
            (content.occurrence.regionMap pattern.val.diagram.root) :=
        Or.inl rootRetained
      let next := batchReconstructionSnoc priorState.state content step
        rfl priorNodeStateExact
        (result.atoms.drop (priorSteps.length + 1)) (by
          rw [priorState.pendingOriginsExact, pendingHead])
        freshRegionsNew freshNodesNew freshWiresNew boundaryRetained
          boundaryWireExact rootCovered (by
          apply Fin.ext
          have sourceRegionExact :
              step.sourceRegion =
                result.regionImage
                  (content.occurrence.regionMap
                    pattern.val.diagram.root) rootRetainedMember := by
            have sameNode := step.sourceNodeExact
            rw [applicationExact, result.atom_generated] at sameNode
            have regionExact :=
              entries.occurrenceRegion_eq_selectionRegion content contentMember
            have siteRegionExact :
                (sites.get site).region =
                  content.occurrence.regionMap pattern.val.diagram.root := by
              have selectedRegionExact := congrArg
                ConcreteWireQuantifier.RelationSeverSite.region siteExact
              change (sites.get site).region = content.selection.region
                at selectedRegionExact
              simpa [Occurrence.maps_root, regionExact] using
                selectedRegionExact
            have siteRetainedMember := result.siteRegion_survives site
            have sourceFromSite :
                step.sourceRegion =
                  result.regionImage (sites.get site).region
                    siteRetainedMember := by
              simpa using (CNode.atom.inj sameNode).1.symm
            have regionImage_congr :
                ∀ (left right : source.val.RegionId)
                  (leftMember : left ∈
                    ConcreteWireQuantifier.Internal.retainedRegions source
                      (sites.flatMap
                        ConcreteWireQuantifier.RelationSeverSite.removedRegions))
                  (rightMember : right ∈
                    ConcreteWireQuantifier.Internal.retainedRegions source
                      (sites.flatMap
                        ConcreteWireQuantifier.RelationSeverSite.removedRegions)),
                  left = right →
                    result.regionImage left leftMember =
                      result.regionImage right rightMember := by
              intro left right leftMember rightMember same
              subst right
              rfl
            exact sourceFromSite.trans
              (regionImage_congr _ _ siteRetainedMember rootRetainedMember
                siteRegionExact)
          change
            (step.checkedFragmentRegion pattern.val.diagram.root).val =
              (step.checkedPriorRegion
                (priorState.state.regionImage
                  ⟨content.occurrence.regionMap pattern.val.diagram.root,
                    rootCovered⟩)).val
          rw [step.checkedPriorRegion_val]
          calc
            (step.checkedFragmentRegion pattern.val.diagram.root).val =
                step.site.val := by
              simp [ConcreteWireQuantifier.RelationJoinStep.checkedFragmentRegion,
                ConcreteSpliceAttachment.fragmentRegion,
                ConcreteSpliceAttachment.hostRegion]
            _ = (step.baseRegionImage step.sourceRegion).val := by
              rw [step.siteExact]
            _ = (step.priorRegionImage step.sourceRegion).val := by
              rw [step.baseRegionImageExact]
              rfl
            _ = step.sourceRegion.val := step.priorRegionImageVal _
            _ = (result.regionImage
                  (content.occurrence.regionMap pattern.val.diagram.root)
                  rootRetainedMember).val := congrArg Fin.val sourceRegionExact
            _ = (ConcreteWireQuantifier.Internal.retainedRegionIndex source
                  (sites.flatMap
                    ConcreteWireQuantifier.RelationSeverSite.removedRegions)
                  (content.occurrence.regionMap pattern.val.diagram.root)
                  rootRetainedMember).val :=
              result.regionImage_val _ rootRetainedMember
            _ = (priorState.state.regionImage
                  ⟨content.occurrence.regionMap pattern.val.diagram.root,
                    rootCovered⟩).val := by
              symm
              exact priorState.state.retainedRegionImage_val _ rootRetained)
      have nextPending :
          next.pendingOrigins =
            result.atoms.drop (priorSteps ++ [step]).length := by
        dsimp [next, batchReconstructionSnoc]
        simp
      exact ⟨contentsDecomposition ▸
        { state := next
          pendingOriginsExact := nextPending
          joinNodeImageExact := by
            dsimp [next, batchReconstructionSnoc]
            exact HEq.rfl
          representedWiresAvoidDying := by
            intro wire same
            by_cases old : BatchCoveredWire sites prefixContents wire.1
            · have priorDyingEq :
                  step.priorWireImage result.relationWire = priorDying :=
                eq_of_heq priorDyingExact
              have priorImageEq :
                  step.checkedPriorWire (priorState.state.wireImage
                      ⟨wire.1, old⟩) =
                    step.checkedPriorWire
                      (step.priorWireImage result.relationWire) := by
                simpa [next, batchReconstructionSnoc, old,
                  step.checkedWireImageExact, step.baseWireImageExact] using
                  same
              have representedEq :=
                step.checkedPriorWire_injective priorImageEq
              exact priorState.representedWiresAvoidDying ⟨wire.1, old⟩
                (by simpa [priorDyingEq] using representedEq)
            · let fresh := newlyCoveredWire content wire.1 wire.2 old
              exact step.checkedFragmentWire_ne_checkedPriorWire_of_internal
                fresh.choose fresh.choose_spec.1
                (step.priorWireImage result.relationWire) (by
                  simpa [next, batchReconstructionSnoc, old,
                    step.checkedWireImageExact,
                    step.baseWireImageExact] using same) }⟩

/-- The complete accepted inverse trace has a construction-owned carrier
state over the entire checked occurrence family. -/
private theorem RelationSeverConcreteReceipt.fullReconstructionState_exists
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Nonempty
      (BatchReconstructionTraceState (steps := receipt.inverse.steps)
        receipt.result occurrences
        receipt.inverse.boundFinal receipt.inverse.boundNodeImage
          receipt.inverse.boundDying) := by
  have contentsLength :
      occurrences.length = receipt.inverse.steps.length := by
    exact
      (receipt.sites_occurrences_length.symm.trans
        receipt.inverseSteps_sites_length.symm)
  have stepsAtomsLength :
      receipt.inverse.steps.length = receipt.result.atoms.length := by
    calc
      receipt.inverse.steps.length =
          (receipt.inverse.steps.map
            ConcreteWireQuantifier.RelationJoinStep.application).length := by
        simp
      _ = receipt.result.atoms.length :=
        congrArg List.length receipt.inverseStepsExact
  have applicationsExact :
      receipt.inverse.steps.map
          ConcreteWireQuantifier.RelationJoinStep.application =
        receipt.result.atoms.take receipt.inverse.steps.length := by
    calc
      receipt.inverse.steps.map
          ConcreteWireQuantifier.RelationJoinStep.application =
        receipt.result.atoms := receipt.inverseStepsExact
      _ = receipt.result.atoms.take receipt.inverse.steps.length := by
        rw [stepsAtomsLength]
        simp
  exact batchReconstructionTraceFold_exists receipt.result occurrences
    receipt.extractions.first receipt.extractions.entries
    receipt.extractions.entries.semanticEvidence_sites receipt.parameters
    receipt.parametersAccepted receipt.inverse.args
      receipt.inverse.relation_signature receipt.inverse.semantic_trace
      occurrences []
      (by simp) contentsLength applicationsExact

private noncomputable def
    RelationSeverConcreteReceipt.fullReconstructionState
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    BatchReconstructionTraceState (steps := receipt.inverse.steps)
      receipt.result occurrences
      receipt.inverse.boundFinal receipt.inverse.boundNodeImage
        receipt.inverse.boundDying :=
  Classical.choice receipt.fullReconstructionState_exists

private theorem
    RelationSeverConcreteReceipt.fullReconstruction_pendingOriginsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.fullReconstructionState.state.pendingOrigins = [] := by
  rw [receipt.fullReconstructionState.pendingOriginsExact]
  have stepsAtomsLength :
      receipt.inverse.steps.length = receipt.result.atoms.length := by
    calc
      receipt.inverse.steps.length =
          (receipt.inverse.steps.map
            ConcreteWireQuantifier.RelationJoinStep.application).length := by
        simp
      _ = receipt.result.atoms.length :=
        congrArg List.length receipt.inverseStepsExact
  rw [stepsAtomsLength]
  simp

private theorem
    RelationSeverConcreteReceipt.fullReconstruction_pendingApplicationsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.fullReconstructionState.state.pendingApplications = [] := by
  rw [receipt.fullReconstructionState.state.pendingApplicationsExact,
    receipt.fullReconstruction_pendingOriginsEmpty]
  rfl

/-- Reindex the completed fold by the occurrence-owned concrete site list,
the authoritative index used by the coverage theorems. -/
private noncomputable def
    RelationSeverConcreteReceipt.completeCarrierState
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    BatchReconstructionState
      (occurrences.map ContentOccurrence.toConcreteSite) occurrences
      receipt.inverse.boundFinal receipt.result.checked := by
  have sitesExact :=
    receipt.extractions.entries.semanticEvidence_sites
  exact sitesExact ▸ receipt.fullReconstructionState.state

private noncomputable def
    RelationSeverConcreteReceipt.completeRegionImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.RegionId → receipt.inverse.boundFinal.val.RegionId :=
  fun region => receipt.fullReconstructionState.state.regionImage
    ⟨region, by
      change BatchCoveredRegion
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences region
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.regionCoverage region⟩

private noncomputable def
    RelationSeverConcreteReceipt.completeNodeImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.NodeId → receipt.inverse.boundFinal.val.NodeId :=
  fun node => receipt.fullReconstructionState.state.nodeImage
    ⟨node, by
      change BatchCoveredNode
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences node
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.nodeCoverage node⟩

private noncomputable def
    RelationSeverConcreteReceipt.completeWireImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.WireId → receipt.inverse.boundFinal.val.WireId :=
  fun wire => receipt.fullReconstructionState.state.wireImage
    ⟨wire, by
      change BatchCoveredWire
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences wire
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.wireCoverage wire⟩

private noncomputable def
    RelationSeverConcreteReceipt.completePortImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    Data.Finite.FiniteEquiv CPort CPort :=
  receipt.fullReconstructionState.state.portImage
    ⟨node, by
      change BatchCoveredNode
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences node
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.nodeCoverage node⟩

private theorem RelationSeverConcreteReceipt.completeRegionImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completeRegionImage := by
  intro left right same
  exact Subtype.ext_iff.mp
    (receipt.fullReconstructionState.state.regionImage_injective same)

private theorem RelationSeverConcreteReceipt.completeRegionImage_sheet
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region : source.val.RegionId)
    (data : source.val.regions region = .sheet) :
    receipt.inverse.boundFinal.val.regions
        (receipt.completeRegionImage region) = .sheet := by
  exact receipt.fullReconstructionState.state.regionSheetExact
    ⟨region, by
      change BatchCoveredRegion
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences region
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.regionCoverage region⟩ data

private theorem RelationSeverConcreteReceipt.completeRegionImage_cut
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    receipt.inverse.boundFinal.val.regions
        (receipt.completeRegionImage region) =
      .cut (receipt.completeRegionImage parent) := by
  exact receipt.fullReconstructionState.state.regionCutExact
    ⟨region, by
      change BatchCoveredRegion
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences region
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.regionCoverage region⟩ parent data

private theorem RelationSeverConcreteReceipt.completeNodeImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completeNodeImage := by
  intro left right same
  exact Subtype.ext_iff.mp
    (receipt.fullReconstructionState.state.nodeImage_injective same)

private theorem RelationSeverConcreteReceipt.completeNodeImage_data
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    receipt.inverse.boundFinal.val.nodes
        (receipt.completeNodeImage node) =
      (source.val.nodes node).relocate
        (receipt.completeRegionImage (source.val.nodes node).region) := by
  exact receipt.fullReconstructionState.state.nodeTableExact
    ⟨node, by
      change BatchCoveredNode
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences node
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.nodeCoverage node⟩

private noncomputable def
    RelationSeverConcreteReceipt.completePlainRegionImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.RegionId → receipt.inverse.plainFinal.val.RegionId :=
  fun region => receipt.inverse.plainBoundRegionImage
    (receipt.completeRegionImage region)

private theorem
    RelationSeverConcreteReceipt.completePlainRegionImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completePlainRegionImage := by
  intro left right same
  apply receipt.completeRegionImage_injective
  exact receipt.inverse.plainBoundRegionImage_injective same

private theorem
    RelationSeverConcreteReceipt.completePlainRegionImage_sheet
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region : source.val.RegionId)
    (data : source.val.regions region = .sheet) :
    receipt.inverse.plainFinal.val.regions
        (receipt.completePlainRegionImage region) = .sheet :=
  receipt.inverse.plainBoundRegionImage_sheet _
    (receipt.completeRegionImage_sheet region data)

private theorem
    RelationSeverConcreteReceipt.completePlainRegionImage_cut
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    receipt.inverse.plainFinal.val.regions
        (receipt.completePlainRegionImage region) =
      .cut (receipt.completePlainRegionImage parent) :=
  receipt.inverse.plainBoundRegionImage_cut _ _
    (receipt.completeRegionImage_cut region parent data)

private noncomputable def
    RelationSeverConcreteReceipt.completePlainNodeImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.NodeId → receipt.inverse.plainFinal.val.NodeId :=
  fun node => receipt.inverse.plainBoundNodeImage
    (receipt.completeNodeImage node)

private theorem
    RelationSeverConcreteReceipt.completePlainNodeImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completePlainNodeImage := by
  intro left right same
  apply receipt.completeNodeImage_injective
  exact receipt.inverse.plainBoundNodeImage_injective same

private theorem
    RelationSeverConcreteReceipt.completePlainNodeImage_data
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    receipt.inverse.plainFinal.val.nodes
        (receipt.completePlainNodeImage node) =
      (source.val.nodes node).relocate
        (receipt.completePlainRegionImage
          (source.val.nodes node).region) := by
  have deleted := receipt.inverse.plainBoundNodeImage_data
    (receipt.completeNodeImage node)
  rw [receipt.completeNodeImage_data] at deleted
  simpa [RelationSeverConcreteReceipt.completePlainNodeImage,
    RelationSeverConcreteReceipt.completePlainRegionImage,
    CNode.relocate_relocate, CNode.region_relocate] using deleted

private theorem RelationSeverConcreteReceipt.completeWireImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completeWireImage := by
  intro left right same
  exact Subtype.ext_iff.mp
    (receipt.fullReconstructionState.state.wireImage_injective same)

private theorem RelationSeverConcreteReceipt.completeWireImage_signature
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.boundFinal.val.wires
      (receipt.completeWireImage wire)).sig =
        (source.val.wires wire).sig := by
  exact receipt.fullReconstructionState.state.wireSignatureExact
    ⟨wire, by
      change BatchCoveredWire
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences wire
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.wireCoverage wire⟩

private theorem RelationSeverConcreteReceipt.completeWireImage_scope
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.boundFinal.val.wires
      (receipt.completeWireImage wire)).scope =
        receipt.completeRegionImage (source.val.wires wire).scope := by
  have fullScope := receipt.fullReconstructionState.state.wireScopeExact
    ⟨wire, by
      change BatchCoveredWire
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences wire
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.wireCoverage wire⟩
  exact fullScope

private theorem
    RelationSeverConcreteReceipt.completeWireImage_ne_boundDying
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    receipt.completeWireImage wire ≠ receipt.inverse.boundDying := by
  simpa [RelationSeverConcreteReceipt.completeWireImage] using
    receipt.fullReconstructionState.representedWiresAvoidDying
      ⟨wire, by
        change BatchCoveredWire
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences wire
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.wireCoverage wire⟩

/-- Exact source-wire landing after the exhausted inverse relation is
deleted from the completed bound reconstruction. -/
private noncomputable def
    RelationSeverConcreteReceipt.completePlainWireImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.WireId → receipt.inverse.plainFinal.val.WireId :=
  fun wire => receipt.inverse.plainBoundWireImage
    (receipt.completeWireImage wire)
    (receipt.completeWireImage_ne_boundDying wire)

private theorem
    RelationSeverConcreteReceipt.completePlainWireImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completePlainWireImage := by
  intro left right same
  apply receipt.completeWireImage_injective
  exact receipt.inverse.plainBoundWireImage_injective
    (receipt.completeWireImage_ne_boundDying left)
    (receipt.completeWireImage_ne_boundDying right) same

private theorem
    RelationSeverConcreteReceipt.completePlainWireImage_signature
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.completePlainWireImage wire)).sig =
        (source.val.wires wire).sig :=
  (receipt.inverse.plainBoundWireImage_signature _
    (receipt.completeWireImage_ne_boundDying wire)).trans
      (receipt.completeWireImage_signature wire)

private theorem
    RelationSeverConcreteReceipt.completePlainWireImage_scope
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.completePlainWireImage wire)).scope =
        receipt.completePlainRegionImage (source.val.wires wire).scope := by
  unfold RelationSeverConcreteReceipt.completePlainWireImage
    RelationSeverConcreteReceipt.completePlainRegionImage
  rw [receipt.inverse.plainBoundWireImage_scope _
    (receipt.completeWireImage_ne_boundDying wire)]
  rw [receipt.completeWireImage_scope]

private theorem
    RelationSeverConcreteReceipt.completePlainEndpoint_mem
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires wire).endpoints) :
    ({ node := receipt.completePlainNodeImage endpoint.node
       port := receipt.completePortImage endpoint.node endpoint.port } :
        CEndpoint receipt.inverse.plainFinal.val.nodeCount) ∈
      (receipt.inverse.plainFinal.val.wires
        (receipt.completePlainWireImage wire)).endpoints := by
  have boundIncident :=
    receipt.fullReconstructionState.state.wireEndpointForward
      ⟨wire, by
        change BatchCoveredWire
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences wire
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.wireCoverage wire⟩
      endpoint incident (by
        change BatchCoveredNode
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences endpoint.node
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.nodeCoverage endpoint.node)
  have deleted := receipt.inverse.plainBoundWireImage_endpoint_mem
    (receipt.completeWireImage wire)
    (receipt.completeWireImage_ne_boundDying wire)
    { node := receipt.completeNodeImage endpoint.node
      port := receipt.completePortImage endpoint.node endpoint.port }
    boundIncident
  exact deleted

private theorem
    RelationSeverConcreteReceipt.inverseSteps_identityRequestsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    ∀ step ∈ receipt.inverse.steps,
      step.attachment.identityRequests = [] := by
  intro step member
  obtain ⟨position, stepExact⟩ := List.get_of_mem member
  subst step
  exact receipt.inverseStep_identityRequestsEmpty position

private theorem
    RelationSeverConcreteReceipt.constructionRegionCount_eq
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.regionCount = receipt.inverse.plainFinal.val.regionCount := by
  have traceCounts := relationJoinTrace_count_exact
    receipt.inverse.semantic_trace receipt.inverseSteps_identityRequestsEmpty
  have removedLength :
      ((receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedRegions).length =
      occurrences.length *
        (pattern.val.diagram.regionsList.filter fun region =>
          decide (region ≠ pattern.val.diagram.root)).length := by
    change
      ((receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedRegions).length = _
    rw [receipt.extractions.entries.semanticEvidence_sites]
    exact receipt.extractions.entries.removedRegions_length
  have stepsLength : receipt.inverse.steps.length = occurrences.length :=
    receipt.inverseSteps_sites_length.trans receipt.sites_occurrences_length
  have partition := receipt.result.retainedRegions_length_add_removedRegions_length
  have severCount := receipt.result.checkedRegionCount_eq_retainedRegions
  have finalCount := receipt.inverse.plainFinal_regionCount
  rcases traceCounts with ⟨traceRegion, _traceNode, _traceWire⟩
  rw [stepsLength, severCount, ← finalCount] at traceRegion
  rw [removedLength] at partition
  omega

private theorem
    RelationSeverConcreteReceipt.constructionNodeCount_eq
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.nodeCount = receipt.inverse.plainFinal.val.nodeCount := by
  have traceCounts := relationJoinTrace_count_exact
    receipt.inverse.semantic_trace receipt.inverseSteps_identityRequestsEmpty
  have removedLength :
      ((receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedNodes).length =
      occurrences.length * pattern.val.diagram.nodeCount := by
    change
      ((receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedNodes).length = _
    rw [receipt.extractions.entries.semanticEvidence_sites]
    exact receipt.extractions.entries.removedNodes_length
  have stepsLength : receipt.inverse.steps.length = occurrences.length :=
    receipt.inverseSteps_sites_length.trans receipt.sites_occurrences_length
  have sitesLength :
      (receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site).length =
          occurrences.length := receipt.sites_occurrences_length
  have partition := receipt.result.retainedNodes_length_add_removedNodes_length
  have severCount := receipt.result.checkedNodeCount_eq_retainedNodes_add_sites
  have finalCount := receipt.inverse.plainFinal_nodeCount
  rcases traceCounts with ⟨_traceRegion, traceNode, _traceWire⟩
  rw [stepsLength, severCount, sitesLength, ← finalCount] at traceNode
  rw [removedLength] at partition
  omega

private theorem
    RelationSeverConcreteReceipt.constructionWireCount_eq
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.wireCount = receipt.inverse.plainFinal.val.wireCount := by
  have traceCounts := relationJoinTrace_count_exact
    receipt.inverse.semantic_trace receipt.inverseSteps_identityRequestsEmpty
  have removedLength :
      ((receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedWires).length =
      occurrences.length *
        (pattern.val.diagram.wiresList.filter fun wire =>
          decide (wire ∉ pattern.val.boundary)).length := by
    change
      ((receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedWires).length = _
    rw [receipt.extractions.entries.semanticEvidence_sites]
    exact receipt.extractions.entries.removedWires_length
  have stepsLength : receipt.inverse.steps.length = occurrences.length :=
    receipt.inverseSteps_sites_length.trans receipt.sites_occurrences_length
  have partition := receipt.result.retainedWires_length_add_removedWires_length
  have severCount := receipt.result.checkedWireCount_eq_retainedWires_add_one
  have finalCount := receipt.inverse.plainFinal_wireCount_add_one
  rcases traceCounts with ⟨_traceRegion, _traceNode, traceWire⟩
  rw [stepsLength, severCount, ← finalCount] at traceWire
  rw [removedLength] at partition
  omega

private noncomputable def
    RelationSeverConcreteReceipt.constructionRegionEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv source.val.RegionId
      receipt.inverse.plainFinal.val.RegionId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin receipt.completePlainRegionImage
    ⟨receipt.completePlainRegionImage_injective,
      Data.Finite.fin_surjective_of_injective_of_card_eq
        receipt.completePlainRegionImage
        receipt.completePlainRegionImage_injective
        receipt.constructionRegionCount_eq⟩

private theorem RelationSeverConcreteReceipt.constructionRegionRoot
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.constructionRegionEquiv source.val.root =
      receipt.inverse.plainFinal.val.root := by
  change receipt.completePlainRegionImage source.val.root =
    receipt.inverse.plainFinal.val.root
  have mappedSheet := receipt.completePlainRegionImage_sheet source.val.root
    source.property.root_is_sheet
  have onlyRoot :=
    (List.all_eq_true.mp
      receipt.inverse.plainFinal.property.only_root_is_sheet)
      (receipt.completePlainRegionImage source.val.root)
      (Data.Finite.mem_allFin _)
  exact (of_decide_eq_true onlyRoot) mappedSheet

private theorem RelationSeverConcreteReceipt.constructionRegionTable
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region : source.val.RegionId) :
    receipt.inverse.plainFinal.val.regions
        (receipt.constructionRegionEquiv region) =
      (source.val.regions region).rename receipt.constructionRegionEquiv := by
  change receipt.inverse.plainFinal.val.regions
      (receipt.completePlainRegionImage region) =
    (source.val.regions region).rename receipt.constructionRegionEquiv
  cases data : source.val.regions region with
  | sheet =>
      simpa [data, CRegion.rename] using
        receipt.completePlainRegionImage_sheet region data
  | cut parent =>
      simpa [data, CRegion.rename] using
        receipt.completePlainRegionImage_cut region parent data

private noncomputable def
    RelationSeverConcreteReceipt.constructionNodeEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv source.val.NodeId
      receipt.inverse.plainFinal.val.NodeId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin receipt.completePlainNodeImage
    ⟨receipt.completePlainNodeImage_injective,
      Data.Finite.fin_surjective_of_injective_of_card_eq
        receipt.completePlainNodeImage
        receipt.completePlainNodeImage_injective
        receipt.constructionNodeCount_eq⟩

private theorem RelationSeverConcreteReceipt.constructionNodeTable
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    receipt.inverse.plainFinal.val.nodes
        (receipt.constructionNodeEquiv node) =
      (source.val.nodes node).rename receipt.constructionRegionEquiv := by
  change receipt.inverse.plainFinal.val.nodes
      (receipt.completePlainNodeImage node) =
    (source.val.nodes node).rename receipt.constructionRegionEquiv
  rw [CNode.rename_eq_relocate]
  exact receipt.completePlainNodeImage_data node

private noncomputable def
    RelationSeverConcreteReceipt.constructionWireEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv source.val.WireId
      receipt.inverse.plainFinal.val.WireId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin receipt.completePlainWireImage
    ⟨receipt.completePlainWireImage_injective,
      Data.Finite.fin_surjective_of_injective_of_card_eq
        receipt.completePlainWireImage
        receipt.completePlainWireImage_injective
        receipt.constructionWireCount_eq⟩

private theorem RelationSeverConcreteReceipt.constructionWireSignature
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.constructionWireEquiv wire)).sig =
        (source.val.wires wire).sig := by
  change (receipt.inverse.plainFinal.val.wires
    (receipt.completePlainWireImage wire)).sig = _
  exact receipt.completePlainWireImage_signature wire

private theorem RelationSeverConcreteReceipt.constructionWireScope
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.constructionWireEquiv wire)).scope =
        receipt.constructionRegionEquiv (source.val.wires wire).scope := by
  change (receipt.inverse.plainFinal.val.wires
    (receipt.completePlainWireImage wire)).scope =
      receipt.completePlainRegionImage (source.val.wires wire).scope
  exact receipt.completePlainWireImage_scope wire

/-- Opaque accepted strongest relation-join transformation. -/
structure AppliedMonolithicRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) where
  private mk ::
  target : CheckedDiagram definitions
  applications : List source.val.NodeId
  private checked :
    RelationJoinReceipt source input.orientation input.wire input.content
      input.parameters target applications

/-- Opaque accepted strongest relation-sever transformation. -/
structure AppliedMonolithicRelationSever
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationSeverInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private polarity :
    CheckedSeverPolarity source input.orientation input.scope
  private concrete :
    RelationSeverConcreteReceipt source input.orientation input.scope
      input.pattern input.occurrences target
  private inverseInput : MonolithicRelationJoinInput target
  private inverseApplied :
    AppliedMonolithicRelationJoin target inverseInput

namespace AppliedMonolithicRelationSever

/--
The exact virtual join already checked as part of a strongest-form sever
receipt.  This is exposed only so the authoring-layer primitive compiler can
reverse that checked construction; the monolithic action remains absent from
the durable proof-step language.
-/
def inverseJoinInput
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    MonolithicRelationJoinInput applied.target :=
  applied.inverseInput

/--
The already-accepted virtual inverse join retained by a strongest-form sever.
The primitive compiler consumes this receipt directly, so sever compilation
does not re-run or strengthen the monolithic acceptance boundary.
-/
def inverseJoinApplied
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationSeverInput source}
    (applied : AppliedMonolithicRelationSever source input) :
    AppliedMonolithicRelationJoin applied.target applied.inverseJoinInput :=
  applied.inverseApplied

end AppliedMonolithicRelationSever

namespace AppliedMonolithicRelationJoin

/-- The concrete strongest-form construction retained by the accepted receipt. -/
def concreteResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    ConcreteWireQuantifier.RelationJoinResult source input.wire input.content
      input.parameters :=
  applied.checked.result

/-- The public target is exactly the concrete strongest-form result. -/
theorem target_eq_concreteResult
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    applied.target = applied.concreteResult.checked :=
  applied.checked.targetExact

/-- Every endpoint of the accepted source relation is an applied atom head. -/
theorem endpoint_applied
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires input.wire).endpoints) :
    endpoint.port = .head ∧
      ∃ region,
        source.val.nodes endpoint.node =
          .atom region applied.concreteResult.args :=
  applied.concreteResult.endpoint_applied endpoint member

private theorem sourceSites_exists
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    ∃ all,
      WirePrimitive.checkAllAppliedSites source input.wire = some all := by
  apply WirePrimitive.checkAllAppliedSites_complete
  intro endpoint member
  obtain ⟨head, region, nodeData⟩ :=
    applied.endpoint_applied endpoint member
  exact ⟨head, region, applied.concreteResult.args, nodeData⟩

/--
The exhaustive checker-owned source sites implied by an accepted strongest
join.  This is derived from checked concrete incidence, not retained as a
second authority in the monolithic receipt.
-/
def sourceSites
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    WirePrimitive.AllAppliedSites source input.wire :=
  match accepted :
      WirePrimitive.checkAllAppliedSites source input.wire with
  | some sites => sites
  | none => by
      exfalso
      obtain ⟨sites, complete⟩ := applied.sourceSites_exists
      rw [accepted] at complete
      contradiction

/-- The executable exhaustive-site checker accepts the derived source sites. -/
theorem sourceSites_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    WirePrimitive.checkAllAppliedSites source input.wire =
      some applied.sourceSites :=
  by
    unfold sourceSites
    split
    next sites accepted => exact accepted
    next accepted =>
      obtain ⟨sites, complete⟩ := applied.sourceSites_exists
      rw [accepted] at complete
      contradiction

/-- The checker-owned site compilation at the dying relation's scope. -/
def sourceSite
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    SiteCompilation source (source.val.wires input.wire).scope :=
  applied.checked.polarity.compiled

/-- The source-site compiler returned the exact polarity receipt used here. -/
theorem sourceSite_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    compileSite? source (source.val.wires input.wire).scope =
      some applied.sourceSite :=
  applied.checked.polarity.compiledAccepted

/-- Exact enclosing-scope evidence for every ordered ambient parameter. -/
theorem parameter_encloses
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input)
    (position : Fin input.parameters.length) :
    source.val.Encloses
      (source.val.wires (input.parameters.get position)).scope
      (source.val.wires input.wire).scope :=
  applied.checked.parameterScopes position

/-- The exact relation argument signature accepted by the monolithic checker. -/
def arguments
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    List Sig :=
  applied.checked.arguments

theorem sourceSignature
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (source.val.wires input.wire).sig = .rel applied.arguments :=
  applied.checked.sourceSignature

theorem boundaryLength
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    input.content.val.boundary.length =
      applied.arguments.length + input.parameters.length :=
  applied.checked.boundaryLength

theorem formalSignatures
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (input.content.val.boundary.take applied.arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      applied.arguments :=
  applied.checked.formalSignatures

theorem parameterSignatures
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    (input.content.val.boundary.drop applied.arguments.length).map
        (fun wire => (input.content.val.diagram.wires wire).sig) =
      input.parameters.map (fun wire => (source.val.wires wire).sig) :=
  applied.checked.parameterSignatures

/-- The consumed relation head is not also an ambient parameter. -/
theorem live_not_parameter
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    input.wire ∉ input.parameters :=
  applied.checked.liveNotParameter

/--
The exact checked open-content compilation retained by an accepted strongest
join.  The authoring compiler may inspect this structural receipt; primitive
checkers still receive only their own local inputs.
-/
def contentCompilation
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    OpenCompilation input.content :=
  applied.checked.contentCompilation.compilation

/-- The executable open compiler returned that exact structural receipt. -/
theorem contentCompilation_accepted
    {source : CheckedDiagram definitions}
    {input : MonolithicRelationJoinInput source}
    (applied : AppliedMonolithicRelationJoin source input) :
    compileOpen input.content = some applied.contentCompilation :=
  applied.checked.contentCompilation.accepted

end AppliedMonolithicRelationJoin

private def requireSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except MonolithicWireQuantifierError
      (CheckedSeverPolarity source orientation scope) := by
  match accepted : compileSite? source scope with
  | none => exact .error .occurrenceOutsideScope
  | some compiled =>
      if legal : severPolarityLegal orientation
          compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, accepted, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .severRequiresPositive
          | .backward => .severBackwardRequiresNegative

private def requireJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except MonolithicWireQuantifierError
      (CheckedJoinPolarity source orientation scope) := by
  match accepted : compileSite? source scope with
  | none => exact .error .occurrenceOutsideScope
  | some compiled =>
      if legal : joinPolarityLegal orientation
          compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, accepted, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .joinRequiresNegative
          | .backward => .joinBackwardRequiresPositive

private def validateOccurrence
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first : ContentOccurrence source pattern)
    (content : ContentOccurrence source pattern) :
    Except MonolithicWireQuantifierError
      (CheckedOccurrence scope first content) := by
  match WireQuantifierSemantics.checkRelationSeverOccurrence
      content.selection content.occurrence with
  | .error error => exact .error (.extractionRejected error)
  | .ok extraction =>
      if !formalBoundaryValid content then
        exact .error .formalNotOnBoundary
      else if contained :
          source.val.Encloses scope content.selection.region then
        if boundaryExact :
            content.occurrence.boundaryAttachments =
              content.formals ++ content.parameters then
          if formalSigsExact :
              first.formalSigs = content.formalSigs then
            if parametersExact :
                first.parameters = content.parameters then
              if positionsExact :
                  first.formalBoundaryPositions? =
                    content.formalBoundaryPositions? then
                exact .ok
                  { extraction := extraction
                    boundaryExact := boundaryExact
                    contained := contained
                    parametersExact := parametersExact.symm }
              else
                exact .error .contentMismatch
            else
              exact .error .parameterMismatch
          else
            exact .error .formalSignatureMismatch
        else
          exact .error .contentMismatch
      else
        exact .error .occurrenceOutsideScope

private def validateOccurrences
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (scope : source.val.RegionId)
    (first : ContentOccurrence source pattern) :
    (contents : List (ContentOccurrence source pattern)) →
      Except MonolithicWireQuantifierError
        (CheckedOccurrenceList scope first contents)
  | [] => .ok .nil
  | content :: rest => do
      let checked ← validateOccurrence scope first content
      let tail ← validateOccurrences scope first rest
      pure (.cons checked tail)

private def validateRelationSever
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (scope : source.val.RegionId)
    (pattern : CheckedOpenDiagram definitions)
    (occurrences : List (ContentOccurrence source pattern)) :
    Except MonolithicWireQuantifierError
      (CheckedSeverPolarity source orientation scope ×
        CheckedOccurrences scope occurrences) := by
  let polarityResult := requireSeverPolarity source orientation scope
  match occurrences with
  | [] => exact .error .emptyOccurrenceList
  | first :: rest =>
      match polarityResult with
      | .error error => exact .error error
      | .ok polarity => exact do
          let extractions ←
            validateOccurrences scope first (first :: rest)
          if disjoint :
              pairwiseDisjoint (first :: rest) = true then
            if parametersAccepted :
                parametersEnclose source scope first.parameters = true then
              pure
                (polarity,
                  { first := first
                    rest := rest
                    contentsExact := rfl
                    entries := extractions
                    disjoint := disjoint
                    parameterScopes :=
                      parametersEnclose_of_true source scope first.parameters
                        parametersAccepted })
            else
              throw .parameterOutsideScope
          else
            throw .occurrencesOverlap

private def validateRelationJoin
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except MonolithicWireQuantifierError
      (CheckedRelationJoin source orientation wire content parameters) := do
  let relation := source.val.wires wire
  let signatureData ←
    match sourceSignature : relation.sig with
    | .iota => throw .expectedRelation
    | .rel args =>
        pure
          (⟨args, sourceSignature⟩ :
            { arguments : List Sig // relation.sig = .rel arguments })
  let args := signatureData.val
  let polarity ← requireJoinPolarity source orientation relation.scope
  let contentCompilation ←
    match accepted : compileOpen content with
    | none => throw .contentCompilationFailed
    | some compilation =>
        pure
          { compilation := compilation
            accepted := accepted }
  let liveNotParameter ←
    if liveParameter : wire ∈ parameters then
      (throw .dyingWireIsParameter :
        Except MonolithicWireQuantifierError (PLift (wire ∉ parameters)))
    else
      pure ⟨liveParameter⟩
  let contentSigs := boundarySigs content
  let split ←
    match splitAccepted : splitAt? args.length contentSigs with
    | none => throw .boundaryTooShort
    | some split =>
        pure
          (⟨split, splitAccepted⟩ :
            { split : List Sig × List Sig //
              splitAt? args.length contentSigs = some split })
  let formalExact ←
    if exact : split.val.1 = args then
      (pure ⟨exact⟩ :
        Except MonolithicWireQuantifierError
          (PLift (split.val.1 = args)))
    else
      (throw .boundarySignatureMismatch :
        Except MonolithicWireQuantifierError
          (PLift (split.val.1 = args)))
  let parameterLengthExact ←
    if exact : split.val.2.length = parameters.length then
      (pure ⟨exact⟩ :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2.length = parameters.length)))
    else
      (throw .parameterMismatch :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2.length = parameters.length)))
  let parameterSigs :=
    parameters.map (fun parameter => (source.val.wires parameter).sig)
  let parameterExact ←
    if exact : split.val.2 = parameterSigs then
      (pure ⟨exact⟩ :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2 = parameterSigs)))
    else
      (throw .parameterMismatch :
        Except MonolithicWireQuantifierError
          (PLift (split.val.2 = parameterSigs)))
  have splitExact :
      (contentSigs.take args.length, contentSigs.drop args.length) =
        split.val := by
    have splitAccepted := split.property
    unfold splitAt? at splitAccepted
    split at splitAccepted
    · exact Option.some.inj splitAccepted
    · simp at splitAccepted
  if accepted :
      parametersEnclose source relation.scope parameters = true then
    let applications ←
      match collectApplications? source wire args with
      | none => throw .nonAppliedEndpoint
      | some applications => pure applications
    pure
      { arguments := args
        sourceSignature := signatureData.property
        boundaryLength := by
          have dropExact :=
            congrArg (fun parts => parts.2.length) splitExact
          have dropLength :
              contentSigs.length - args.length = parameters.length := by
            simpa [List.length_drop] using
              dropExact.trans parameterLengthExact.down
          have argsBound : args.length ≤ contentSigs.length := by
            have splitAccepted := split.property
            unfold splitAt? at splitAccepted
            split at splitAccepted
            · assumption
            · simp at splitAccepted
          have contentLength :
              contentSigs.length =
                args.length + parameters.length := by
            omega
          simpa [contentSigs, boundarySigs] using contentLength
        formalSignatures := by
          have exact :=
            (congrArg Prod.fst splitExact).trans formalExact.down
          simpa [contentSigs, boundarySigs, List.map_take] using exact
        parameterSignatures := by
          have exact :=
            (congrArg Prod.snd splitExact).trans parameterExact.down
          simpa [contentSigs, boundarySigs, parameterSigs,
            List.map_drop] using exact
        liveNotParameter := liveNotParameter.down
        polarity := polarity
        applications := applications.map (·.node)
        contentCompilation := contentCompilation
        parameterScopes :=
          parametersEnclose_of_true source relation.scope parameters accepted }
  else
    throw .parameterOutsideScope

/--
Validate and apply one strongest sever.  All structure is computed by the
concrete owner; callers cannot supply a target or a semantic certificate.
-/
def applyMonolithicRelationSever
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationSeverInput source) :
    Except MonolithicWireQuantifierError
      (AppliedMonolithicRelationSever source input) := by
  match validateRelationSever input.orientation input.scope input.pattern
      input.occurrences with
  | .error error => exact .error error
  | .ok validated =>
      let polarity := validated.1
      let extractions := validated.2
      let sites :=
        extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site
      match accepted :
          ConcreteWireQuantifier.severRelation source input.scope sites with
      | .error error => exact .error (.concreteRejected error)
      | .ok result =>
          match parametersAccepted :
              extractions.first.parameters.mapM result.wireImage? with
          | none => exact .error .parameterTransportFailed
          | some parameters =>
              match validateRelationJoin
                  (oppositeOrientation input.orientation)
                  result.relationWire input.pattern parameters with
              | .error _ => exact .error .inverseRelationJoinRejected
              | .ok inverseChecked =>
                  match inverseAccepted :
                      ConcreteWireQuantifier.joinRelation result.checked
                        result.relationWire input.pattern parameters with
                  | .error _ =>
                      exact .error .inverseRelationJoinRejected
                  | .ok inverse =>
                      match inverseIsoAccepted :
                          ConcreteIsoSearch.findConcreteIso?
                            inverse.plainFinal.val source.val with
                      | none =>
                          exact .error .inverseReconstructionRejected
                      | some inverseIso =>
                          exact .ok
                            (AppliedMonolithicRelationSever.mk
                              result.checked polarity
                              { extractions := extractions
                                result := result
                                accepted := accepted
                                targetExact := rfl
                                parameters := parameters
                                parametersAccepted := parametersAccepted
                                inverseChecked := inverseChecked
                                inverse := inverse
                                inverseAccepted := inverseAccepted
                                inverseStepsExact := by
                                  calc
                                    inverse.steps.map
                                          ConcreteWireQuantifier.RelationJoinStep.application =
                                        inverse.applications :=
                                      inverse.steps_application_order
                                    _ = result.atoms := by
                                      rw [inverse.applications_storage_order]
                                      exact
                                        result.relationApplications_storage_order
                                inverseIso := inverseIso }
                              { orientation :=
                                  oppositeOrientation input.orientation
                                wire := result.relationWire
                                content := input.pattern
                                parameters := parameters }
                              (AppliedMonolithicRelationJoin.mk
                                inverse.checked inverse.applications
                                { arguments := inverseChecked.arguments
                                  sourceSignature :=
                                    inverseChecked.sourceSignature
                                  boundaryLength :=
                                    inverseChecked.boundaryLength
                                  formalSignatures :=
                                    inverseChecked.formalSignatures
                                  parameterSignatures :=
                                    inverseChecked.parameterSignatures
                                  liveNotParameter :=
                                    inverseChecked.liveNotParameter
                                  polarity := inverseChecked.polarity
                                  contentCompilation :=
                                    inverseChecked.contentCompilation
                                  result := inverse
                                  accepted := inverseAccepted
                                  targetExact := rfl
                                  applicationsExact := rfl
                                  parameterScopes :=
                                    inverseChecked.parameterScopes }))

/--
Validate and apply one strongest join.  Relation joining consumes every
endpoint; no subset of applications is accepted.
-/
def applyMonolithicRelationJoin
    (source : CheckedDiagram definitions)
    (input : MonolithicRelationJoinInput source) :
    Except MonolithicWireQuantifierError
      (AppliedMonolithicRelationJoin source input) := by
  match validateRelationJoin input.orientation input.wire input.content
      input.parameters with
  | .error error => exact .error error
  | .ok validated =>
      match accepted :
          ConcreteWireQuantifier.joinRelation source input.wire input.content
            input.parameters with
      | .error error => exact .error (.concreteRejected error)
      | .ok result =>
          exact .ok
            (AppliedMonolithicRelationJoin.mk
              result.checked result.applications
              { arguments := validated.arguments
                sourceSignature := validated.sourceSignature
                boundaryLength := validated.boundaryLength
                formalSignatures := validated.formalSignatures
                parameterSignatures := validated.parameterSignatures
                liveNotParameter := validated.liveNotParameter
                polarity := validated.polarity
                contentCompilation := validated.contentCompilation
                result := result
                accepted := accepted
                targetExact := rfl
                applicationsExact := rfl
                parameterScopes := validated.parameterScopes })

/--
Relation-content abstraction is sound in the direction selected by the
checker-owned sever polarity. The accepted receipt contains a checked inverse
join and an independently checked reconstruction isomorphism; callers supply
no semantic evidence.
-/
theorem relation_sever_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (scope : source.val.RegionId)
    (pattern : CheckedOpenDiagram definitions)
    (occurrences : List (ContentOccurrence source pattern))
    (applied :
      AppliedMonolithicRelationSever source
        { orientation := orientation
          scope := scope
          pattern := pattern
          occurrences := occurrences })
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  let checked := applied.concrete
  obtain ⟨_relationFamily, _relationLaw, sound⟩ :=
    ConcreteWireQuantifier.RelationSeverInsertionSemantics.inverseJoinDenotes
      checked.inverse
        checked.inverseChecked.contentCompilation.compilation
        checked.inverseChecked.polarity.compiled
        checked.inverseChecked.parameterScopes checked.inverseIso
        model definitionEnv
  rw [checked.targetExact]
  cases orientation with
  | forward =>
      have even :
          checked.inverseChecked.polarity.compiled.frame.context.cutDepth %
              2 =
            0 :=
        of_decide_eq_true (by
          simpa [oppositeOrientation, joinPolarityLegal] using
            checked.inverseChecked.polarity.legal)
      exact sound.1 even
  | backward =>
      have odd :
          checked.inverseChecked.polarity.compiled.frame.context.cutDepth %
              2 =
            1 :=
        of_decide_eq_true (by
          simpa [oppositeOrientation, joinPolarityLegal] using
            checked.inverseChecked.polarity.legal)
      exact sound.2 odd

/--
Relation-content grounding is sound in the direction selected by the
checker-owned polarity receipt.
-/
theorem relation_join_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (applied :
      AppliedMonolithicRelationJoin source
        { orientation := orientation
          wire := wire
          content := content
          parameters := parameters })
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.contentCompilation.compilation
      checked.polarity.compiled model definitionEnv checked.parameterScopes
  rw [checked.targetExact]
  cases orientation with
  | forward =>
      have odd :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using checked.polarity.legal)
      exact sound.2 odd
  | backward =>
      have even :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using checked.polarity.legal)
      exact sound.1 even

end MonolithicWireQuantifier

export MonolithicWireQuantifier
  (ContentOccurrence MonolithicRelationSeverInput
    MonolithicRelationJoinInput MonolithicWireQuantifierError
    AppliedMonolithicRelationSever AppliedMonolithicRelationJoin
    applyMonolithicRelationSever applyMonolithicRelationJoin
    relation_sever_sound relation_join_sound)

end VisualProof
