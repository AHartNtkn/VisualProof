import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.WireQuantifierRelationSever
import VisualProof.Diagram.Concrete.WireQuantifierRelationSeverSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRaw
import VisualProof.Rule.Orientation

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

namespace Internal
def severPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

def joinPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

def oppositeOrientation : Orientation → Orientation
  | .forward => .backward
  | .backward => .forward

structure CheckedSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  compiledAccepted : compileSite? source scope = some compiled
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

structure CheckedJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  compiledAccepted : compileSite? source scope = some compiled
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

def endpointMember
    (endpoint : CEndpoint nodeCount)
    (endpoints : List (CEndpoint nodeCount)) : Bool :=
  decide (endpoint ∈ endpoints)

def listsIntersect [DecidableEq α]
    (left right : List α) : Bool :=
  left.any fun value => decide (value ∈ right)

def occurrenceOverlaps
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

def pairwiseDisjoint
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
structure CheckedOccurrence
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

theorem checkedOccurrence_allRegions
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

theorem checkedOccurrence_region
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

theorem checkedOccurrence_allNodes
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

theorem checkedOccurrence_internalWires
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

theorem CheckedOccurrence.removedRegions_length
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

theorem CheckedOccurrence.removedNodes_length
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

theorem CheckedOccurrence.removedWires_length
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
inductive CheckedOccurrenceList
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
structure CheckedOccurrences
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

def CheckedOccurrenceList.semanticEvidence
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

theorem CheckedOccurrenceList.semanticEvidence_sites
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
theorem CheckedOccurrenceList.properRegion_mem_removedRegions
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

theorem CheckedOccurrenceList.nodeImage_mem_removedNodes
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

theorem CheckedOccurrenceList.internalWireImage_mem_removedWires
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

theorem CheckedOccurrenceList.occurrenceRegion_eq_selectionRegion
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

theorem CheckedOccurrenceList.removedRegions_length
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

theorem CheckedOccurrenceList.removedNodes_length
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

theorem CheckedOccurrenceList.removedWires_length
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

def CheckedOccurrenceList.get :
    (entries : CheckedOccurrenceList scope first contents) →
    (position : Fin contents.length) →
    CheckedOccurrence scope first (contents.get position)
  | .nil, position => Fin.elim0 position
  | .cons checked tail, position =>
      Fin.cases (by simpa using checked)
        (fun rest => by
          simpa [List.get_eq_getElem] using tail.get rest)
        position

def CheckedOccurrences.semanticEvidence
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

def retainedBySitesRegion
    {source : CheckedDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (region : source.val.RegionId) : Prop :=
  region ∉ sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedRegions

def retainedBySitesNode
    {source : CheckedDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (node : source.val.NodeId) : Prop :=
  node ∉ sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedNodes

def retainedBySitesWire
    {source : CheckedDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (wire : source.val.WireId) : Prop :=
  wire ∉ sites.flatMap ConcreteWireQuantifier.RelationSeverSite.removedWires

def restoredRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (region : source.val.RegionId) : Prop :=
  ∃ content ∈ restored, ∃ patternRegion,
    patternRegion ≠ pattern.val.diagram.root ∧
      content.occurrence.regionMap patternRegion = region

def restoredNode
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (node : source.val.NodeId) : Prop :=
  ∃ content ∈ restored, ∃ patternNode,
    content.occurrence.nodeMap patternNode = node

def restoredWire
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (wire : source.val.WireId) : Prop :=
  ∃ content ∈ restored, ∃ patternWire,
    patternWire ∉ pattern.val.boundary ∧
      content.occurrence.wireMap patternWire = wire

/-- Explicit carrier images for the restored prefix.  These lists are the
computational authority for deciding whether a carrier is already represented;
the existential predicates below remain proof-facing specifications. -/
def restoredRegionImages
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern)) :
    List source.val.RegionId :=
  restored.flatMap fun content =>
    (pattern.val.diagram.regionsList.filter fun region =>
      decide (region ≠ pattern.val.diagram.root)).map
        content.occurrence.regionMap

def restoredNodeImages
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern)) :
    List source.val.NodeId :=
  restored.flatMap fun content =>
    pattern.val.diagram.nodesList.map content.occurrence.nodeMap

def restoredWireImages
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern)) :
    List source.val.WireId :=
  restored.flatMap fun content =>
    (pattern.val.diagram.wiresList.filter fun wire =>
      decide (wire ∉ pattern.val.boundary)).map content.occurrence.wireMap

theorem mem_restoredRegionImages_iff
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (region : source.val.RegionId) :
    region ∈ restoredRegionImages restored ↔ restoredRegion restored region := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with
      ⟨content, contentMember, imageMember⟩
    rcases List.mem_map.mp imageMember with
      ⟨patternRegion, properMember, mapped⟩
    exact ⟨content, contentMember, patternRegion,
      of_decide_eq_true (List.mem_filter.mp properMember).2, mapped⟩
  · rintro ⟨content, contentMember, patternRegion, nonroot, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨content, contentMember, List.mem_map.mpr ⟨patternRegion, ?_, rfl⟩⟩
    exact List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin patternRegion, decide_eq_true nonroot⟩

theorem mem_restoredNodeImages_iff
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (node : source.val.NodeId) :
    node ∈ restoredNodeImages restored ↔ restoredNode restored node := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with
      ⟨content, contentMember, imageMember⟩
    rcases List.mem_map.mp imageMember with
      ⟨patternNode, _patternMember, mapped⟩
    exact ⟨content, contentMember, patternNode, mapped⟩
  · rintro ⟨content, contentMember, patternNode, rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨content, contentMember,
      List.mem_map.mpr
        ⟨patternNode, Data.Finite.mem_allFin patternNode, rfl⟩⟩

theorem mem_restoredWireImages_iff
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (restored : List (ContentOccurrence source pattern))
    (wire : source.val.WireId) :
    wire ∈ restoredWireImages restored ↔ restoredWire restored wire := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with
      ⟨content, contentMember, imageMember⟩
    rcases List.mem_map.mp imageMember with
      ⟨patternWire, internalMember, mapped⟩
    exact ⟨content, contentMember, patternWire,
      of_decide_eq_true (List.mem_filter.mp internalMember).2, mapped⟩
  · rintro ⟨content, contentMember, patternWire, internal, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨content, contentMember, List.mem_map.mpr ⟨patternWire, ?_, rfl⟩⟩
    exact List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin patternWire, decide_eq_true internal⟩

def BatchCoveredRegion
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (region : source.val.RegionId) : Prop :=
  retainedBySitesRegion sites region ∨ restoredRegion restored region

def BatchCoveredNode
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (node : source.val.NodeId) : Prop :=
  retainedBySitesNode sites node ∨ restoredNode restored node

def BatchCoveredWire
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (wire : source.val.WireId) : Prop :=
  retainedBySitesWire sites wire ∨ restoredWire restored wire

def batchCoveredRegionDecidable
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (region : source.val.RegionId) :
    Decidable (BatchCoveredRegion sites restored region) := by
  exact decidable_of_iff
    (region ∉ sites.flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedRegions ∨
      region ∈ restoredRegionImages restored)
    (by rw [mem_restoredRegionImages_iff]; rfl)

def batchCoveredNodeDecidable
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (node : source.val.NodeId) :
    Decidable (BatchCoveredNode sites restored node) := by
  exact decidable_of_iff
    (node ∉ sites.flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedNodes ∨
      node ∈ restoredNodeImages restored)
    (by rw [mem_restoredNodeImages_iff]; rfl)

def batchCoveredWireDecidable
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (sites : List (ConcreteWireQuantifier.RelationSeverSite source))
    (restored : List (ContentOccurrence source pattern))
    (wire : source.val.WireId) :
    Decidable (BatchCoveredWire sites restored wire) := by
  exact decidable_of_iff
    (wire ∉ sites.flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedWires ∨
      wire ∈ restoredWireImages restored)
    (by rw [mem_restoredWireImages_iff]; rfl)

theorem CheckedOccurrenceList.regionCoverage
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

theorem CheckedOccurrenceList.nodeCoverage
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

theorem CheckedOccurrenceList.wireCoverage
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
theorem properRegion_not_covered_before
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

theorem nodeImage_not_covered_before
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

theorem internalWireImage_not_covered_before
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
theorem denseIndex_injective
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

def PortDataCorresponds
    (left : CNode leftRegionCount definitionCount)
    (right : CNode rightRegionCount definitionCount)
    (leftPort rightPort : CPort) : Prop :=
  match left, right with
  | .identity _ leftSig leftArity, .identity _ rightSig rightArity =>
      leftSig = rightSig ∧ leftArity = rightArity ∧
        ∃ leftIndex rightIndex,
          leftPort = .identity leftIndex ∧ rightPort = .identity rightIndex
  | _, _ => rightPort = leftPort

def requiredPortsForNode
    (node : CNode regionCount definitionCount) : List CPort :=
  match node with
  | .atom _ args => CPort.head :: (List.range args.length).map CPort.arg
  | .ref _ _ args => (List.range args.length).map CPort.arg
  | .identity _ _ arity => (List.range arity).map CPort.identity

@[simp] theorem requiredPortsForNode_relocate
    (node : CNode regionCount definitionCount)
    (region : Fin targetRegionCount) :
    requiredPortsForNode (node.relocate region) = requiredPortsForNode node := by
  cases node <;> rfl

theorem portDataCorresponds_refl_relocate
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

structure BatchReconstructionState
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
def completeRegionImage
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
def completeNodeImage
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
def completeWireImage
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

def formalBoundaryValid
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    (content : ContentOccurrence source pattern) : Bool :=
  content.formals.all fun wire =>
    decide (wire ∈ content.occurrence.boundaryAttachments)

def parametersEnclose
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (parameters : List source.val.WireId) : Bool :=
  parameters.all fun wire =>
    decide (source.val.Encloses (source.val.wires wire).scope scope)

theorem parametersEnclose_of_true
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

def boundarySigs
    (content : CheckedOpenDiagram definitions) : List Sig :=
  content.val.boundary.map fun wire =>
    (content.val.diagram.wires wire).sig

def splitAt? (count : Nat) (values : List α) :
    Option (List α × List α) :=
  if count ≤ values.length then
    some (values.take count, values.drop count)
  else
    none

structure RelationApplication
    (source : CheckedDiagram definitions)
    (args : List Sig) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId

def argumentWires?
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

def applicationAt?
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

def collectApplications?
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

structure CheckedOpenCompilation
    (content : CheckedOpenDiagram definitions) where
  compilation : OpenCompilation content
  accepted : compileOpen content = some compilation

structure CheckedRelationJoin
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

structure RelationSeverConcreteReceipt
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
    ConcreteWireQuantifier.joinRelation result.checked
        result.relationWire pattern parameters =
      .ok inverse
  inverseStepsExact :
    inverse.steps.map
        ConcreteWireQuantifier.RelationJoinStep.application =
      result.atoms


end Internal

end MonolithicWireQuantifier

end VisualProof
