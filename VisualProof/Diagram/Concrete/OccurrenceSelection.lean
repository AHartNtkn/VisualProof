import VisualProof.Diagram.Concrete.OccurrenceEmbedding

namespace VisualProof.Diagram

open VisualProof.Data.Finite

namespace OccurrenceProblem

/-- Content-region indices which are direct children of the effective root. -/
def rootChildren (problem : OccurrenceProblem signature) :
    List problem.ContentRegion :=
  filterFin fun region => decide
    ((problem.pattern.val.diagram.regions
      (ContentRegion.origin problem region)).parent? =
      some problem.binderSpine.bodyContainer)

/-- Content-node indices owned directly by the effective root. -/
def rootNodes (problem : OccurrenceProblem signature) :
    List problem.ContentNode :=
  filterFin fun node => decide
    ((problem.pattern.val.diagram.nodes
      (ContentNode.origin problem node)).region =
      problem.binderSpine.bodyContainer)

/-- Internal-wire indices scoped directly at the effective root. -/
def rootInternalWires (problem : OccurrenceProblem signature) :
    List problem.InternalWire :=
  filterFin fun wire => decide
    ((problem.pattern.val.diagram.wires
      (InternalWire.origin problem wire)).scope =
      problem.binderSpine.bodyContainer)

@[simp] theorem mem_rootChildren (problem : OccurrenceProblem signature)
    (region : problem.ContentRegion) :
    region ∈ problem.rootChildren ↔
      (problem.pattern.val.diagram.regions
        (ContentRegion.origin problem region)).parent? =
        some problem.binderSpine.bodyContainer := by
  simp [rootChildren]

@[simp] theorem mem_rootNodes (problem : OccurrenceProblem signature)
    (node : problem.ContentNode) :
    node ∈ problem.rootNodes ↔
      (problem.pattern.val.diagram.nodes
        (ContentNode.origin problem node)).region =
        problem.binderSpine.bodyContainer := by
  simp [rootNodes]

@[simp] theorem mem_rootInternalWires (problem : OccurrenceProblem signature)
    (wire : problem.InternalWire) :
    wire ∈ problem.rootInternalWires ↔
      (problem.pattern.val.diagram.wires
        (InternalWire.origin problem wire)).scope =
        problem.binderSpine.bodyContainer := by
  simp [rootInternalWires]

theorem ContentRegion.body_encloses
    (problem : OccurrenceProblem signature)
    (region : problem.ContentRegion) :
    problem.pattern.val.diagram.Encloses problem.binderSpine.bodyContainer
      (region.origin problem) := by
  rcases region.origin_is_content problem with hroot | hmaterial
  · rw [hroot]
    exact ConcreteDiagram.Encloses.refl _ _
  · exact hmaterial.2

/-- Every direct child of the effective body is material rather than an
administrative sheet or binder proxy. -/
theorem directChildOfBody_material (problem : OccurrenceProblem signature)
    (region : problem.PatternRegion)
    (parent :
      (problem.pattern.val.diagram.regions region).parent? =
        some problem.binderSpine.bodyContainer) :
    problem.binderSpine.IsMaterialRegion region := by
  have hneRoot : region ≠ problem.pattern.val.diagram.root := by
    intro equality
    subst region
    rw [problem.pattern.property.diagram_well_formed.root_is_sheet] at parent
    simp [CRegion.parent?] at parent
  refine ⟨hneRoot, ?_⟩
  intro index equality
  subst region
  rw [problem.binderSpine.proxy_region] at parent
  simp only [CRegion.parent?] at parent
  split at parent
  · rename_i hzero
    have hnonempty : problem.binderSpine.proxyCount ≠ 0 := by
      have := index.isLt
      omega
    have hbody :=
      problem.binderSpine.body_eq_terminal_of_nonempty hnonempty
    rw [hbody] at parent
    exact problem.binderSpine.proxy_ne_root
      ⟨problem.binderSpine.proxyCount - 1, by omega⟩
      (Option.some.inj parent).symm
  · rename_i hnonzero
    have hcountNonzero : problem.binderSpine.proxyCount ≠ 0 := by
      have := index.isLt
      omega
    have hbody :=
      problem.binderSpine.body_eq_terminal_of_nonempty hcountNonzero
    rw [hbody] at parent
    have hindices := problem.binderSpine.proxy_injective
      (Option.some.inj parent)
    have hvals := congrArg Fin.val hindices
    simp only at hvals
    have := index.isLt
    omega

theorem directChild_contentIndex (problem : OccurrenceProblem signature)
    (region : problem.PatternRegion)
    (parent :
      (problem.pattern.val.diagram.regions region).parent? =
        some problem.binderSpine.bodyContainer) :
    ∃ content : problem.ContentRegion,
      content.origin problem = region := by
  have hmaterial := problem.directChildOfBody_material region parent
  have hencloses : problem.pattern.val.diagram.Encloses
      problem.binderSpine.bodyContainer region := by
    refine ⟨⟨1, by have := region.isLt; omega⟩, ?_⟩
    simp [ConcreteDiagram.climb, parent]
  have hcontent : problem.IsContentRegion region :=
    Or.inr ⟨hmaterial, hencloses⟩
  apply (FilteredFiber.survives_iff_exists_origin
    problem.contentRegionBool region).1
  simp [contentRegionBool, hcontent]

end OccurrenceProblem

namespace RawOccurrenceCertificate

variable {problem : OccurrenceProblem signature}

/-- Host child roots named by the occurrence, with defensive duplicate erasure. -/
def selectedChildRoots (raw : RawOccurrenceCertificate problem) :
    List problem.HostRegion :=
  (problem.rootChildren.map raw.regionMap).eraseDups

/-- Host nodes selected directly at the occurrence anchor. -/
def selectedDirectNodes (raw : RawOccurrenceCertificate problem) :
    List problem.HostNode :=
  (problem.rootNodes.map raw.nodeMap).eraseDups

/-- Host wires explicitly selected at the occurrence anchor. -/
def selectedExplicitWires (raw : RawOccurrenceCertificate problem) :
    List problem.HostWire :=
  (problem.rootInternalWires.map fun wire =>
    raw.wireMap (wire.origin problem)).eraseDups

/-- The host-side selection request denoted by raw occurrence maps. -/
def selectionRequest (raw : RawOccurrenceCertificate problem) :
    SelectionRequest problem.host.val where
  anchor := raw.anchor
  childRoots := raw.selectedChildRoots
  directNodes := raw.selectedDirectNodes
  explicitWires := raw.selectedExplicitWires

@[simp] theorem selectionRequest_anchor
    (raw : RawOccurrenceCertificate problem) :
    raw.selectionRequest.anchor = raw.anchor := rfl

theorem selectedChildRoots_nodup (raw : RawOccurrenceCertificate problem) :
    raw.selectedChildRoots.Nodup :=
  eraseDups_nodup _

theorem selectedDirectNodes_nodup (raw : RawOccurrenceCertificate problem) :
    raw.selectedDirectNodes.Nodup :=
  eraseDups_nodup _

theorem selectedExplicitWires_nodup (raw : RawOccurrenceCertificate problem) :
    raw.selectedExplicitWires.Nodup :=
  eraseDups_nodup _

theorem mem_selectedChildRoots_iff (raw : RawOccurrenceCertificate problem)
    (region : problem.HostRegion) :
    region ∈ raw.selectedChildRoots ↔
      ∃ source ∈ problem.rootChildren, raw.regionMap source = region := by
  simp [selectedChildRoots]

theorem mem_selectedDirectNodes_iff (raw : RawOccurrenceCertificate problem)
    (node : problem.HostNode) :
    node ∈ raw.selectedDirectNodes ↔
      ∃ source ∈ problem.rootNodes, raw.nodeMap source = node := by
  simp [selectedDirectNodes]

theorem mem_selectedExplicitWires_iff
    (raw : RawOccurrenceCertificate problem) (wire : problem.HostWire) :
    wire ∈ raw.selectedExplicitWires ↔
      ∃ source ∈ problem.rootInternalWires,
        raw.wireMap (source.origin problem) = wire := by
  simp [selectedExplicitWires]

end RawOccurrenceCertificate

namespace OpenOccurrenceEmbedding

variable {problem : OccurrenceProblem signature}

theorem rootSubset (embedding : OpenOccurrenceEmbedding problem) :
    embedding.raw.RootSubset :=
  embedding.valid.2.2.1

theorem selectedChildRoots_direct (embedding : OpenOccurrenceEmbedding problem) :
    ∀ region, region ∈ embedding.raw.selectedChildRoots →
      (problem.host.val.regions region).parent? = some embedding.raw.anchor := by
  intro region hregion
  obtain ⟨source, hsource, rfl⟩ :=
    (embedding.raw.mem_selectedChildRoots_iff region).1 hregion
  have hparent := (problem.mem_rootChildren source).1 hsource
  obtain ⟨content, horigin, htarget⟩ :=
    embedding.rootSubset.1 (source.origin problem) hparent
  have hcontent : content = source :=
    FilteredFiber.origin_injective problem.contentRegionBool horigin
  simpa [hcontent] using htarget

theorem selectedDirectNodes_at_anchor
    (embedding : OpenOccurrenceEmbedding problem) :
    ∀ node, node ∈ embedding.raw.selectedDirectNodes →
      (problem.host.val.nodes node).region = embedding.raw.anchor := by
  intro node hnode
  obtain ⟨source, hsource, rfl⟩ :=
    (embedding.raw.mem_selectedDirectNodes_iff node).1 hnode
  have hregion := (problem.mem_rootNodes source).1 hsource
  obtain ⟨content, horigin, htarget⟩ :=
    embedding.rootSubset.2.1 (source.origin problem) hregion
  have hcontent : content = source :=
    FilteredFiber.origin_injective problem.contentNodeBool horigin
  simpa [hcontent] using htarget

theorem selectedExplicitWires_at_anchor
    (embedding : OpenOccurrenceEmbedding problem) :
    ∀ wire, wire ∈ embedding.raw.selectedExplicitWires →
      (problem.host.val.wires wire).scope = embedding.raw.anchor := by
  intro wire hwire
  obtain ⟨source, hsource, rfl⟩ :=
    (embedding.raw.mem_selectedExplicitWires_iff wire).1 hwire
  have hscope := (problem.mem_rootInternalWires source).1 hsource
  have hinternal :=
    FilteredFiber.origin_survives problem.internalWireBool source
  have hnotBoundary : source.origin problem ∉ problem.pattern.val.boundary := by
    simpa [OccurrenceProblem.internalWireBool,
      OccurrenceProblem.boundaryWireBool] using hinternal
  exact embedding.rootSubset.2.2 (source.origin problem)
    hnotBoundary hscope

/-- A source ancestry path strictly below the content root is preserved by the
region embedding. -/
theorem regionMap_encloses (embedding : OpenOccurrenceEmbedding problem)
    (ancestor descendant : problem.ContentRegion)
    (ancestor_proper :
      ancestor.origin problem ≠ problem.binderSpine.bodyContainer)
    (encloses : problem.pattern.val.diagram.Encloses
      (ancestor.origin problem) (descendant.origin problem)) :
    problem.host.val.Encloses (embedding.raw.regionMap ancestor)
      (embedding.raw.regionMap descendant) := by
  obtain ⟨steps, hclimb⟩ := encloses
  rcases steps with ⟨steps, hbound⟩
  induction steps generalizing descendant with
  | zero =>
      have horigin : descendant.origin problem = ancestor.origin problem :=
        Option.some.inj hclimb
      have hindex : descendant = ancestor :=
        FilteredFiber.origin_injective problem.contentRegionBool horigin
      subst descendant
      exact ConcreteDiagram.Encloses.refl _ _
  | succ steps ih =>
      cases hparent :
          (problem.pattern.val.diagram.regions
            (descendant.origin problem)).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hclimb
      | some parent =>
          have htail : problem.pattern.val.diagram.climb steps parent =
              some (ancestor.origin problem) := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          have descendant_proper : descendant.origin problem ≠
              problem.binderSpine.bodyContainer := by
            intro hbody
            have hab : problem.pattern.val.diagram.Encloses
                (ancestor.origin problem)
                problem.binderSpine.bodyContainer :=
              ⟨⟨steps + 1, by omega⟩, by
                simpa [hbody] using hclimb⟩
            have hba := ancestor.body_encloses problem
            exact ancestor_proper
              (ConcreteElaboration.checked_encloses_antisymm
                problem.pattern.property.diagram_well_formed hab hba)
          obtain ⟨mappedParent, howner, htargetParent⟩ :=
            RawOccurrenceCertificate.ProperRegionValid.parent_image
              embedding.raw descendant
              (embedding.valid.proper_region descendant)
              descendant_proper hparent
          rcases embedding.raw.mappedRegionOwner?_eq_some howner with
            hroot | ⟨parentContent, hparentOrigin, hparentMap⟩
          · obtain ⟨hparentBody, _⟩ := hroot
            subst parent
            have hab : problem.pattern.val.diagram.Encloses
                (ancestor.origin problem)
                problem.binderSpine.bodyContainer :=
              ⟨⟨steps, by omega⟩, htail⟩
            have hba := ancestor.body_encloses problem
            exact False.elim (ancestor_proper
              (ConcreteElaboration.checked_encloses_antisymm
                problem.pattern.property.diagram_well_formed hab hba))
          · have htail' : problem.pattern.val.diagram.climb steps
                (parentContent.origin problem) =
                some (ancestor.origin problem) := by
              simpa [hparentOrigin] using htail
            have hancestorParent : problem.host.val.Encloses
                (embedding.raw.regionMap ancestor)
                (embedding.raw.regionMap parentContent) :=
              ih (descendant := parentContent) (by omega) htail'
            have hparentDescendant : problem.host.val.Encloses
                (embedding.raw.regionMap parentContent)
                (embedding.raw.regionMap descendant) := by
              refine ⟨⟨1, by
                have := (embedding.raw.regionMap descendant).isLt
                omega⟩, ?_⟩
              simp [ConcreteDiagram.climb, htargetParent, hparentMap]
            exact ConcreteElaboration.checked_encloses_trans
              problem.host.property hancestorParent hparentDescendant

/-- Every proper content-region image lies in the reconstructed host selection
predicate. -/
theorem mappedProperRegion_selected
    (embedding : OpenOccurrenceEmbedding problem)
    (source : problem.ContentRegion)
    (proper : source.origin problem ≠ problem.binderSpine.bodyContainer) :
    embedding.raw.selectionRequest.SelectsRegion
      (embedding.raw.regionMap source) := by
  have hbodyEncloses := source.body_encloses problem
  obtain ⟨rootChild, hrootParent, hrootEncloses⟩ :=
    ConcreteElaboration.exists_direct_child_enclosing
      problem.pattern.property.diagram_well_formed proper hbodyEncloses
  obtain ⟨rootSource, hrootOrigin⟩ :=
    problem.directChild_contentIndex rootChild hrootParent
  have hrootMember : rootSource ∈ problem.rootChildren := by
    apply (problem.mem_rootChildren rootSource).2
    simpa [hrootOrigin] using hrootParent
  have hrootSelected : embedding.raw.regionMap rootSource ∈
      embedding.raw.selectedChildRoots :=
    (embedding.raw.mem_selectedChildRoots_iff _).2
      ⟨rootSource, hrootMember, rfl⟩
  have hrootProper : rootSource.origin problem ≠
      problem.binderSpine.bodyContainer := by
    intro heq
    have hrootChildEq : rootChild = problem.binderSpine.bodyContainer :=
      hrootOrigin.symm.trans heq
    have hself :
        (problem.pattern.val.diagram.regions
          problem.binderSpine.bodyContainer).parent? =
            some problem.binderSpine.bodyContainer := by
      simpa [hrootChildEq] using hrootParent
    exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
      problem.pattern.property.diagram_well_formed hself)
      (ConcreteDiagram.Encloses.refl _ _)
  have hsourceEncloses : problem.pattern.val.diagram.Encloses
      (rootSource.origin problem) (source.origin problem) := by
    simpa [hrootOrigin] using hrootEncloses
  have htargetEncloses := embedding.regionMap_encloses rootSource source
    hrootProper hsourceEncloses
  exact ⟨embedding.raw.regionMap rootSource, hrootSelected,
    htargetEncloses⟩

theorem mappedNode_selected (embedding : OpenOccurrenceEmbedding problem)
    (sourceNode : problem.ContentNode) :
    embedding.raw.selectionRequest.SelectsNode
      (embedding.raw.nodeMap sourceNode) := by
  let sourceIndex := sourceNode.origin problem
  let sourceRegion :=
    (problem.pattern.val.diagram.nodes sourceIndex).region
  have hnodeValid := embedding.valid.nodes sourceNode
  have howner : embedding.raw.mappedRegionOwner? sourceRegion =
      some (problem.host.val.nodes
        (embedding.raw.nodeMap sourceNode)).region := by
    simpa [RawOccurrenceCertificate.NodeValid, sourceIndex, sourceRegion]
      using hnodeValid.1
  have hcontentSurvives :=
    FilteredFiber.origin_survives problem.contentNodeBool sourceNode
  have hregionSurvives : problem.contentRegionBool sourceRegion = true := by
    simpa [OccurrenceProblem.contentNodeBool, sourceIndex, sourceRegion]
      using hcontentSurvives
  obtain ⟨sourceRegionIndex, hregionIndex, hregionOrigin⟩ :=
    FilteredFiber.exists_index_of_survives problem.contentRegionBool
      sourceRegion hregionSurvives
  have hregionOrigin' :
      OccurrenceProblem.ContentRegion.origin problem sourceRegionIndex =
        sourceRegion := by
    simpa [sourceRegion] using hregionOrigin
  by_cases hroot : sourceRegion = problem.binderSpine.bodyContainer
  · apply Or.inl
    apply (embedding.raw.mem_selectedDirectNodes_iff _).2
    refine ⟨sourceNode, ?_, rfl⟩
    apply (problem.mem_rootNodes sourceNode).2
    exact hroot
  · apply Or.inr
    have hbodyEncloses : problem.pattern.val.diagram.Encloses
        problem.binderSpine.bodyContainer sourceRegion := by
      rw [← hregionOrigin']
      exact OccurrenceProblem.ContentRegion.body_encloses
        problem sourceRegionIndex
    obtain ⟨rootChild, hchildParent, hchildEncloses⟩ :=
      ConcreteElaboration.exists_direct_child_enclosing
        problem.pattern.property.diagram_well_formed hroot hbodyEncloses
    obtain ⟨rootChildIndex, hchildOrigin⟩ :=
      problem.directChild_contentIndex rootChild hchildParent
    have hchildProper : rootChildIndex.origin problem ≠
        problem.binderSpine.bodyContainer := by
      intro equality
      have hsame : rootChild = problem.binderSpine.bodyContainer :=
        hchildOrigin.symm.trans equality
      have hselfParent :
          (problem.pattern.val.diagram.regions
            problem.binderSpine.bodyContainer).parent? =
              some problem.binderSpine.bodyContainer := by
        simpa [hsame] using hchildParent
      exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
        problem.pattern.property.diagram_well_formed hselfParent)
        (ConcreteDiagram.Encloses.refl _ _)
    have hchildMember : rootChildIndex ∈ problem.rootChildren := by
      apply (problem.mem_rootChildren rootChildIndex).2
      simpa [hchildOrigin] using hchildParent
    have hselectedChild : embedding.raw.regionMap rootChildIndex ∈
        embedding.raw.selectedChildRoots :=
      (embedding.raw.mem_selectedChildRoots_iff _).2
        ⟨rootChildIndex, hchildMember, rfl⟩
    have hsourceEncloses : problem.pattern.val.diagram.Encloses
        (OccurrenceProblem.ContentRegion.origin problem rootChildIndex)
        (OccurrenceProblem.ContentRegion.origin problem sourceRegionIndex) := by
      rw [hchildOrigin, hregionOrigin']
      exact hchildEncloses
    have hmappedEncloses := embedding.regionMap_encloses
      rootChildIndex sourceRegionIndex hchildProper hsourceEncloses
    have hmappedOwner : embedding.raw.mappedRegionOwner? sourceRegion =
        some (embedding.raw.regionMap sourceRegionIndex) := by
      simp [RawOccurrenceCertificate.mappedRegionOwner?, hroot,
        RawOccurrenceCertificate.regionImage?, hregionIndex]
    have htargetRegion :
        (problem.host.val.nodes (embedding.raw.nodeMap sourceNode)).region =
          embedding.raw.regionMap sourceRegionIndex := by
      exact Option.some.inj (howner.symm.trans hmappedOwner)
    exact ⟨embedding.raw.regionMap rootChildIndex, hselectedChild, by
      simpa [htargetRegion] using hmappedEncloses⟩

theorem selectedExplicitWireEndpoints_selected
    (embedding : OpenOccurrenceEmbedding problem) :
    ∀ wire, wire ∈ embedding.raw.selectedExplicitWires →
      ∀ endpoint,
        endpoint ∈ (problem.host.val.wires wire).endpoints →
          embedding.raw.selectionRequest.SelectsNode endpoint.node := by
  intro wire hwire endpoint hendpoint
  obtain ⟨sourceWire, hsourceWire, rfl⟩ :=
    (embedding.raw.mem_selectedExplicitWires_iff wire).1 hwire
  have hvalid := embedding.valid.internal_wires sourceWire
  have hperm :
      (embedding.raw.mappedEndpoints (sourceWire.origin problem)).Perm
        (problem.host.val.wires
          (embedding.raw.wireMap (sourceWire.origin problem))).endpoints := by
    simpa [RawOccurrenceCertificate.InternalWireValid] using hvalid.2.2
  have hmapped : endpoint ∈
      embedding.raw.mappedEndpoints (sourceWire.origin problem) :=
    hperm.mem_iff.mpr hendpoint
  obtain ⟨sourceEndpoint, hsourceEndpoint, hmap⟩ :=
    List.mem_filterMap.mp hmapped
  unfold RawOccurrenceCertificate.mapEndpoint? at hmap
  cases hnodeImage : embedding.raw.nodeImage? sourceEndpoint.node with
  | none => simp [hnodeImage] at hmap
  | some mappedNode =>
      have hendpointEq :
          ({ node := mappedNode, port := sourceEndpoint.port } :
              CEndpoint problem.host.val.nodeCount) = endpoint := by
        simpa [hnodeImage] using hmap
      unfold RawOccurrenceCertificate.nodeImage? at hnodeImage
      cases hindex : FilteredFiber.index? problem.contentNodeBool
          sourceEndpoint.node with
      | none => simp [hindex] at hnodeImage
      | some sourceNode =>
          rw [hindex] at hnodeImage
          have hmappedNode : embedding.raw.nodeMap sourceNode = mappedNode :=
            Option.some.inj hnodeImage
          have htargetNode : endpoint.node =
              embedding.raw.nodeMap sourceNode := by
            simpa [hmappedNode] using
              congrArg CEndpoint.node hendpointEq.symm
          rw [htargetNode]
          exact embedding.mappedNode_selected sourceNode

/-- The checked host selection denoted by a valid occurrence embedding. -/
def selection (embedding : OpenOccurrenceEmbedding problem) :
    CheckedSelection problem.host.val :=
  ⟨embedding.raw.selectionRequest, {
    childRoots_nodup := embedding.raw.selectedChildRoots_nodup
    childRoots_direct := embedding.selectedChildRoots_direct
    directNodes_nodup := embedding.raw.selectedDirectNodes_nodup
    directNodes_at_anchor := embedding.selectedDirectNodes_at_anchor
    explicitWires_nodup := embedding.raw.selectedExplicitWires_nodup
    explicitWires_at_anchor := embedding.selectedExplicitWires_at_anchor
    explicitWireEndpoints_selected :=
      embedding.selectedExplicitWireEndpoints_selected
  }⟩

theorem selectedRegion_has_image
    (embedding : OpenOccurrenceEmbedding problem)
    (target : problem.HostRegion)
    (selected : target ∈ embedding.selection.selectedRegions) :
    ∃ source : problem.ContentRegion,
      source.origin problem ≠ problem.binderSpine.bodyContainer ∧
        embedding.raw.regionMap source = target := by
  obtain ⟨rootImage, hrootImage, hencloses⟩ :=
    (embedding.selection.mem_selectedRegions target).1 selected
  change rootImage ∈ embedding.raw.selectedChildRoots at hrootImage
  obtain ⟨rootSource, hrootSource, hrootMap⟩ :=
    (embedding.raw.mem_selectedChildRoots_iff rootImage).1 hrootImage
  have hrootParent := (problem.mem_rootChildren rootSource).1 hrootSource
  have hrootProper : rootSource.origin problem ≠
      problem.binderSpine.bodyContainer := by
    intro heq
    have hself :
        (problem.pattern.val.diagram.regions
          problem.binderSpine.bodyContainer).parent? =
            some problem.binderSpine.bodyContainer := by
      simpa [heq] using hrootParent
    exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
      problem.pattern.property.diagram_well_formed hself)
      (ConcreteDiagram.Encloses.refl _ _)
  obtain ⟨steps, hclimb⟩ := hencloses
  rcases steps with ⟨steps, hstepsBound⟩
  have descend : ∀ (count : Nat) (source : problem.ContentRegion)
      (hostRegion : problem.HostRegion),
      source.origin problem ≠ problem.binderSpine.bodyContainer →
      problem.host.val.climb count hostRegion =
        some (embedding.raw.regionMap source) →
      ∃ descendant : problem.ContentRegion,
        descendant.origin problem ≠ problem.binderSpine.bodyContainer ∧
          embedding.raw.regionMap descendant = hostRegion := by
    intro count
    induction count with
    | zero =>
        intro source hostRegion hproper hzero
        have heq : hostRegion = embedding.raw.regionMap source :=
          Option.some.inj hzero
        exact ⟨source, hproper, heq.symm⟩
    | succ count ih =>
        intro source hostRegion hproper hsucc
        cases hparent : (problem.host.val.regions hostRegion).parent? with
        | none => simp [ConcreteDiagram.climb, hparent] at hsucc
        | some hostParent =>
            have htail : problem.host.val.climb count hostParent =
                some (embedding.raw.regionMap source) := by
              simpa [ConcreteDiagram.climb, hparent] using hsucc
            obtain ⟨sourceParent, hsourceParentProper, hsourceParentMap⟩ :=
              ih source hostParent hproper htail
            have hexact := embedding.valid.proper_subtrees sourceParent
              hsourceParentProper
            have hhostChild : hostRegion ∈
                RawOccurrenceCertificate.exactChildren problem.host.val
                  (embedding.raw.regionMap sourceParent) := by
              rw [RawOccurrenceCertificate.mem_exactChildren]
              simpa [hsourceParentMap] using hparent
            have hmappedChild : hostRegion ∈
                (RawOccurrenceCertificate.exactChildren
                    problem.pattern.val.diagram (sourceParent.origin problem)).filterMap
                  embedding.raw.regionImage? :=
              hexact.1.mem_iff.mpr hhostChild
            obtain ⟨sourceRegion, hsourceRegionChild, hsourceRegionImage⟩ :=
              List.mem_filterMap.mp hmappedChild
            unfold RawOccurrenceCertificate.regionImage? at hsourceRegionImage
            cases hindex : FilteredFiber.index? problem.contentRegionBool
                sourceRegion with
            | none => simp [hindex] at hsourceRegionImage
            | some sourceChild =>
                have hchildOrigin := (FilteredFiber.index?_eq_some_iff
                  problem.contentRegionBool sourceRegion sourceChild).1 hindex
                have hchildMap : embedding.raw.regionMap sourceChild =
                    hostRegion := by
                  rw [hindex] at hsourceRegionImage
                  exact Option.some.inj hsourceRegionImage
                have hsourceChildParent :
                    (problem.pattern.val.diagram.regions
                      (OccurrenceProblem.ContentRegion.origin problem
                        sourceChild)).parent? =
                        some (sourceParent.origin problem) := by
                  rw [RawOccurrenceCertificate.mem_exactChildren] at hsourceRegionChild
                  change (problem.pattern.val.diagram.regions
                    (FilteredFiber.origin problem.contentRegionBool sourceChild)).parent? = _
                  rw [hchildOrigin]
                  exact hsourceRegionChild
                have hchildProper :
                    OccurrenceProblem.ContentRegion.origin problem sourceChild ≠
                    problem.binderSpine.bodyContainer := by
                  intro hbody
                  have hparentEnclosesBody :
                      problem.pattern.val.diagram.Encloses
                        (sourceParent.origin problem)
                        problem.binderSpine.bodyContainer := by
                    refine ⟨⟨1, by
                      have := (OccurrenceProblem.ContentRegion.origin problem
                        sourceChild).isLt
                      omega⟩, ?_⟩
                    simp [ConcreteDiagram.climb, ← hbody,
                      hsourceChildParent]
                  have hbodyEnclosesParent :=
                    OccurrenceProblem.ContentRegion.body_encloses
                      problem sourceParent
                  exact hsourceParentProper
                    (ConcreteElaboration.checked_encloses_antisymm
                      problem.pattern.property.diagram_well_formed
                      hparentEnclosesBody hbodyEnclosesParent)
                exact ⟨sourceChild, hchildProper, hchildMap⟩
  rw [← hrootMap] at hclimb
  exact descend steps rootSource target hrootProper (by simpa using hclimb)

/-- Exact carrier characterization used to build extraction-specialized finite
region equivalences. -/
theorem selectedRegion_iff_image
    (embedding : OpenOccurrenceEmbedding problem)
    (target : problem.HostRegion) :
    target ∈ embedding.selection.selectedRegions ↔
      ∃ source : problem.ContentRegion,
        source.origin problem ≠ problem.binderSpine.bodyContainer ∧
          embedding.raw.regionMap source = target := by
  constructor
  · exact embedding.selectedRegion_has_image target
  · rintro ⟨source, proper, rfl⟩
    apply (embedding.selection.mem_selectedRegions _).2
    change embedding.raw.selectionRequest.SelectsRegion
      (embedding.raw.regionMap source)
    exact embedding.mappedProperRegion_selected source proper

theorem selectedNode_iff_image
    (embedding : OpenOccurrenceEmbedding problem)
    (target : problem.HostNode) :
    target ∈ embedding.selection.selectedNodes ↔
      ∃ source : problem.ContentNode,
        embedding.raw.nodeMap source = target := by
  constructor
  · intro selected
    have hsemantic := (embedding.selection.mem_selectedNodes target).1 selected
    change target ∈ embedding.raw.selectedDirectNodes ∨
      embedding.raw.selectionRequest.SelectsRegion
        (problem.host.val.nodes target).region at hsemantic
    rcases hsemantic with hdirect | hregion
    · obtain ⟨source, _, hmap⟩ :=
        (embedding.raw.mem_selectedDirectNodes_iff target).1 hdirect
      exact ⟨source, hmap⟩
    · have hregionMember : (problem.host.val.nodes target).region ∈
          embedding.selection.selectedRegions := by
        apply (embedding.selection.mem_selectedRegions _).2
        change embedding.raw.selectionRequest.SelectsRegion _
        exact hregion
      obtain ⟨sourceRegion, hproper, hregionMap⟩ :=
        (embedding.selectedRegion_iff_image
          (problem.host.val.nodes target).region).1 hregionMember
      have hexact := embedding.valid.proper_subtrees sourceRegion hproper
      have hhostNode : target ∈ RawOccurrenceCertificate.exactNodes
          problem.host.val (embedding.raw.regionMap sourceRegion) := by
        rw [RawOccurrenceCertificate.mem_exactNodes]
        exact hregionMap.symm
      have hmappedNode : target ∈
          (RawOccurrenceCertificate.exactNodes problem.pattern.val.diagram
            (sourceRegion.origin problem)).filterMap
              embedding.raw.nodeImage? :=
        hexact.2.1.mem_iff.mpr hhostNode
      obtain ⟨sourceIndex, hsourceNode, hsourceImage⟩ :=
        List.mem_filterMap.mp hmappedNode
      unfold RawOccurrenceCertificate.nodeImage? at hsourceImage
      cases hindex : FilteredFiber.index? problem.contentNodeBool sourceIndex with
      | none => simp [hindex] at hsourceImage
      | some sourceNode =>
          rw [hindex] at hsourceImage
          exact ⟨sourceNode, Option.some.inj hsourceImage⟩
  · rintro ⟨source, rfl⟩
    apply (embedding.selection.mem_selectedNodes _).2
    change embedding.raw.selectionRequest.SelectsNode
      (embedding.raw.nodeMap source)
    exact embedding.mappedNode_selected source

theorem mappedInternalWire_selected
    (embedding : OpenOccurrenceEmbedding problem)
    (source : problem.InternalWire) :
    embedding.raw.wireMap (source.origin problem) ∈
      embedding.selection.internalWires := by
  have hvalid := embedding.valid.internal_wires source
  have hscope : embedding.raw.mappedRegionOwner?
        (problem.pattern.val.diagram.wires (source.origin problem)).scope =
      some (problem.host.val.wires
        (embedding.raw.wireMap (source.origin problem))).scope := by
    simpa [RawOccurrenceCertificate.InternalWireValid] using hvalid.2.1
  rcases embedding.raw.mappedRegionOwner?_eq_some_proper hscope with
    hroot | ⟨sourceRegion, hregionOrigin, hproper, hregionMap⟩
  · apply (embedding.selection.mem_internalWires _).2
    right
    change embedding.raw.wireMap (source.origin problem) ∈
      embedding.raw.selectedExplicitWires
    apply (embedding.raw.mem_selectedExplicitWires_iff _).2
    refine ⟨source, ?_, rfl⟩
    apply (problem.mem_rootInternalWires source).2
    exact hroot.1
  · apply (embedding.selection.mem_internalWires _).2
    left
    change embedding.raw.selectionRequest.SelectsRegion _
    have hselected := embedding.mappedProperRegion_selected sourceRegion hproper
    simpa [hregionMap] using hselected

theorem selectedInternalWire_iff_image
    (embedding : OpenOccurrenceEmbedding problem)
    (target : problem.HostWire) :
    target ∈ embedding.selection.internalWires ↔
      ∃ source : problem.InternalWire,
        embedding.raw.wireMap (source.origin problem) = target := by
  constructor
  · intro selected
    have hsemantic := (embedding.selection.mem_internalWires target).1 selected
    change embedding.raw.selectionRequest.SelectsRegion
        (problem.host.val.wires target).scope ∨
      target ∈ embedding.raw.selectedExplicitWires at hsemantic
    rcases hsemantic with hscope | hexplicit
    · have hregionMember : (problem.host.val.wires target).scope ∈
          embedding.selection.selectedRegions := by
        apply (embedding.selection.mem_selectedRegions _).2
        change embedding.raw.selectionRequest.SelectsRegion _
        exact hscope
      obtain ⟨sourceRegion, hproper, hregionMap⟩ :=
        (embedding.selectedRegion_iff_image
          (problem.host.val.wires target).scope).1 hregionMember
      have hexact := embedding.valid.proper_subtrees sourceRegion hproper
      have hhostWire : target ∈ ConcreteElaboration.exactScopeWires
          problem.host.val (embedding.raw.regionMap sourceRegion) := by
        rw [ConcreteElaboration.mem_exactScopeWires]
        exact hregionMap.symm
      have hmappedWire : target ∈
          (ConcreteElaboration.exactScopeWires problem.pattern.val.diagram
            (sourceRegion.origin problem)).map embedding.raw.wireMap :=
        hexact.2.2.mem_iff.mpr hhostWire
      obtain ⟨sourceWire, hsourceScope, hsourceMap⟩ :=
        List.mem_map.mp hmappedWire
      have hnotBoundary : sourceWire ∉ problem.pattern.val.boundary := by
        intro hboundary
        have hboundaryScope :=
          problem.terminalBody.boundary_is_root_scoped sourceWire hboundary
        have hsourceScopeEq :=
          (ConcreteElaboration.mem_exactScopeWires
            problem.pattern.val.diagram (sourceRegion.origin problem)
            sourceWire).1 hsourceScope
        rcases sourceRegion.origin_is_content problem with hbody | hmaterial
        · exact hproper hbody
        · exact hmaterial.1.1 (hsourceScopeEq.symm.trans hboundaryScope)
      have hinternal : problem.internalWireBool sourceWire = true := by
        simp [OccurrenceProblem.internalWireBool,
          OccurrenceProblem.boundaryWireBool, hnotBoundary]
      obtain ⟨source, hindex, horigin⟩ :=
        FilteredFiber.exists_index_of_survives problem.internalWireBool
          sourceWire hinternal
      refine ⟨source, ?_⟩
      change embedding.raw.wireMap
        (FilteredFiber.origin problem.internalWireBool source) = target
      rw [horigin]
      exact hsourceMap
    · obtain ⟨source, _, hmap⟩ :=
        (embedding.raw.mem_selectedExplicitWires_iff target).1 hexplicit
      exact ⟨source, hmap⟩
  · rintro ⟨source, rfl⟩
    exact embedding.mappedInternalWire_selected source

/-- Observational matcher equality is canonical host closure plus the ordered
attachment vector. It deliberately forgets source-map association and binders. -/
def SameFootprint (left right : OpenOccurrenceEmbedding problem) : Prop :=
  left.selection.selectedRegions = right.selection.selectedRegions ∧
    left.selection.selectedNodes = right.selection.selectedNodes ∧
    left.selection.internalWires = right.selection.internalWires ∧
    List.ofFn left.raw.attachment = List.ofFn right.raw.attachment

end OpenOccurrenceEmbedding

end VisualProof.Diagram
