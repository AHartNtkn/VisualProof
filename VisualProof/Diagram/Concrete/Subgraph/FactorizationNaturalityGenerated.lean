import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityLocal
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrameSupport

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

theorem hostRegion_injective
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Function.Injective attachment.hostRegion := by
  intro left right same
  apply Fin.ext
  simpa [ConcreteSpliceAttachment.hostRegion] using congrArg Fin.val same

private theorem hostClimb
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (steps : Nat) (region : base.val.RegionId),
      attachment.diagram.climb steps (attachment.hostRegion region) =
        (base.val.climb steps region).map attachment.hostRegion
  | 0, _ => rfl
  | steps + 1, region => by
      cases data : base.val.regions region with
      | sheet =>
          simp only [ConcreteDiagram.climb, compiled.host_region_source,
            mapRegion, data]
          rfl
      | cut parent =>
          simp [ConcreteDiagram.climb, compiled.host_region_source,
            mapRegion, data, hostClimb compiled steps parent]

private theorem climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  simp only [ConcreteDiagram.climb]
  rw [wellFormed.root_is_sheet]

private theorem climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [climb_succ_root_none definitions diagram wellFormed right]
            at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [climb_succ_root_none definitions diagram wellFormed left]
            at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              apply congrArg Nat.succ
              apply induction
              · simpa [ConcreteDiagram.climb, regionData] using leftClimb
              · simpa [ConcreteDiagram.climb, regionData] using rightClimb

private theorem checked_reaches_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (region : diagram.RegionId) :
    ∃ steps : Fin (diagram.regionCount + 1),
      diagram.climb steps region = some diagram.root := by
  have checked :=
    (List.all_eq_true.mp wellFormed.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      diagram diagram.root region).mp (of_decide_eq_true checked)

theorem parent_encloses_child
    (diagram : ConcreteDiagram definitionCount)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    diagram.Encloses parent child := by
  apply
    (ConcreteElaboration.encloses_iff_exists
      diagram parent child).mpr
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, childData]

theorem checked_encloses_antisymm
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {left right : diagram.RegionId}
    (leftRight : diagram.Encloses left right)
    (rightLeft : diagram.Encloses right left) :
    left = right := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram left right).mp
      leftRight
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram right left).mp
      rightLeft
  obtain ⟨rootSteps, rootClimb⟩ :=
    checked_reaches_root definitions diagram wellFormed left
  have loop :
      diagram.climb (rightSteps.val + leftSteps.val) left = some left := by
    rw [climb_add diagram rightSteps.val leftSteps.val left, rightClimb]
    exact leftClimb
  have longerRoot :
      diagram.climb ((rightSteps.val + leftSteps.val) + rootSteps.val)
          left =
        some diagram.root := by
    rw [climb_add diagram
      (rightSteps.val + leftSteps.val) rootSteps.val left, loop]
    exact rootClimb
  have sameDepth :=
    climb_to_root_unique definitions diagram wellFormed
      longerRoot rootClimb
  have rightZero : rightSteps.val = 0 := by omega
  have exactRight := rightClimb
  rw [rightZero] at exactRight
  simpa [ConcreteDiagram.climb] using exactRight

private theorem checked_encloses_comparable
    (diagram : ConcreteDiagram definitionCount)
    {left right descendant : diagram.RegionId}
    (leftEncloses : diagram.Encloses left descendant)
    (rightEncloses : diagram.Encloses right descendant) :
    diagram.Encloses left right ∨ diagram.Encloses right left := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram left descendant).mp
      leftEncloses
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram right descendant).mp
      rightEncloses
  by_cases leftBefore : leftSteps.val ≤ rightSteps.val
  · right
    apply
      (ConcreteElaboration.encloses_iff_exists diagram right left).mpr
    let remaining := rightSteps.val - leftSteps.val
    have sum : leftSteps.val + remaining = rightSteps.val := by omega
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) rightSteps.isLt⟩, ?_⟩
    have composed := climb_add diagram leftSteps.val remaining descendant
    rw [sum, leftClimb, rightClimb] at composed
    exact composed.symm
  · left
    apply
      (ConcreteElaboration.encloses_iff_exists diagram left right).mpr
    let remaining := leftSteps.val - rightSteps.val
    have sum : rightSteps.val + remaining = leftSteps.val := by omega
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) leftSteps.isLt⟩, ?_⟩
    have composed := climb_add diagram rightSteps.val remaining descendant
    rw [sum, rightClimb, leftClimb] at composed
    exact composed.symm

theorem checked_encloses_child_split
    (diagram : ConcreteDiagram definitionCount)
    (ancestor child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent)
    (encloses : diagram.Encloses ancestor child) :
    ancestor = child ∨ diagram.Encloses ancestor parent := by
  obtain ⟨steps, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram ancestor child).mp
      encloses
  cases steps with
  | mk steps bound =>
      cases steps with
      | zero => exact .inl (by simpa using climbed.symm)
      | succ steps =>
          right
          apply
            (ConcreteElaboration.encloses_iff_exists
              diagram ancestor parent).mpr
          exact
            ⟨⟨steps, by omega⟩, by
              simpa [ConcreteDiagram.climb, childData] using climbed⟩

theorem checked_child_ne_parent
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    child ≠ parent := by
  intro same
  subst child
  obtain ⟨steps, climbed⟩ :=
    checked_reaches_root definitions diagram wellFormed parent
  cases steps with
  | mk steps bound =>
      cases steps with
      | zero =>
          have parentRoot : parent = diagram.root := by
            simpa [ConcreteDiagram.climb] using Option.some.inj climbed
          subst parent
          rw [wellFormed.root_is_sheet] at childData
          contradiction
      | succ steps =>
          have longer :
              diagram.climb (steps + 1) parent = some diagram.root := by
            simpa using climbed
          have shorter :
              diagram.climb steps parent = some diagram.root := by
            simpa [ConcreteDiagram.climb, childData] using longer
          have impossible :=
            climb_to_root_unique definitions diagram wellFormed
              longer shorter
          omega

theorem selected_child_encloses_middle
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region child middle site : diagram.RegionId}
    (regionMiddle : diagram.Encloses region middle)
    (middleStrict : middle ≠ region)
    (childData : diagram.regions child = .cut region)
    (childSite : diagram.Encloses child site)
    (middleSite : diagram.Encloses middle site) :
    diagram.Encloses child middle := by
  rcases checked_encloses_comparable diagram childSite middleSite with
    childMiddle | middleChild
  · exact childMiddle
  · rcases checked_encloses_child_split diagram middle child region
        childData middleChild with middleIsChild | middleRegion
    · subst middle
      exact ConcreteDiagram.encloses_refl diagram child
    · have same :=
        checked_encloses_antisymm definitions diagram wellFormed
          regionMiddle middleRegion
      exact False.elim (middleStrict same.symm)

private theorem successfulClimb_le_count
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) (region ancestor : diagram.RegionId)
    (climbed : diagram.climb steps region = some ancestor) :
    steps ≤ diagram.regionCount := by
  have ancestorReaches :
      diagram.Encloses diagram.root ancestor :=
    of_decide_eq_true
      ((List.all_eq_true.mp wellFormed.all_regions_reach_root)
        ancestor (Data.Finite.mem_allFin ancestor))
  obtain ⟨rootSteps, ancestorRoot⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram diagram.root
      ancestor).mp ancestorReaches
  have regionRoot :
      diagram.climb (steps + rootSteps.val) region =
        some diagram.root := by
    rw [climb_add, climbed]
    exact ancestorRoot
  have regionReaches :
      diagram.Encloses diagram.root region :=
    of_decide_eq_true
      ((List.all_eq_true.mp wellFormed.all_regions_reach_root)
        region (Data.Finite.mem_allFin region))
  obtain ⟨bounded, boundedRoot⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram diagram.root
      region).mp regionReaches
  have same :=
    climb_to_root_unique definitions diagram wellFormed regionRoot
      boundedRoot
  omega

private theorem encloses_trans
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram outer middle).mp
      outerMiddle
  obtain ⟨innerSteps, innerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram middle inner).mp
      middleInner
  have combined :
      diagram.climb (innerSteps.val + outerSteps.val) inner =
        some outer := by
    rw [climb_add, innerClimb]
    exact outerClimb
  have bounded :=
    successfulClimb_le_count definitions diagram wellFormed
      (innerSteps.val + outerSteps.val) inner outer combined
  apply (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
  exact ⟨⟨innerSteps.val + outerSteps.val, by omega⟩, combined⟩

private theorem hostEncloses_iff
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (ancestor child : base.val.RegionId) :
    attachment.diagram.Encloses
        (attachment.hostRegion ancestor) (attachment.hostRegion child) ↔
      base.val.Encloses ancestor child := by
  rw [ConcreteElaboration.encloses_iff_exists,
    ConcreteElaboration.encloses_iff_exists]
  constructor
  · rintro ⟨steps, climbed⟩
    have mapped := climbed
    rw [hostClimb compiled] at mapped
    cases source : base.val.climb steps.val child with
    | none => simp [source] at mapped
    | some region =>
        rw [source] at mapped
        have same :=
          hostRegion_injective attachment (Option.some.inj mapped)
        subst region
        have bounded :=
          successfulClimb_le_count definitions base.val base.property
            steps.val child ancestor source
        exact ⟨⟨steps.val, by omega⟩, source⟩
  · rintro ⟨steps, climbed⟩
    let targetSteps : Fin (attachment.diagram.regionCount + 1) :=
      ⟨steps.val, by
        change steps.val < attachment.regionCount + 1
        simp only [ConcreteSpliceAttachment.regionCount]
        omega⟩
    refine ⟨targetSteps, ?_⟩
    rw [hostClimb compiled, climbed]
    rfl

private theorem fragmentClimb_to_root
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (steps : Nat) (region : fragment.val.diagram.RegionId),
      fragment.val.diagram.climb steps region =
          some fragment.val.diagram.root →
        attachment.diagram.climb steps (attachment.fragmentRegion region) =
          some (attachment.hostRegion site)
  | 0, region, climbed => by
      have same : region = fragment.val.diagram.root := by
        exact Option.some.inj climbed
      subst region
      exact congrArg some
        ((compiled.fragmentRegion_eq_site_iff
          fragment.val.diagram.root).mpr rfl)
  | steps + 1, region, climbed => by
      cases data : fragment.val.diagram.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb, data] at climbed
      | cut parent =>
          have nonroot : region ≠ fragment.val.diagram.root := by
            intro same
            subst region
            rw [fragment.property.diagram.root_is_sheet] at data
            contradiction
          have parentClimbed :
              fragment.val.diagram.climb steps parent =
                some fragment.val.diagram.root := by
            simpa [ConcreteDiagram.climb, data] using climbed
          let fresh :=
            DenseList.index attachment.fragmentRegions region (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList, Data.Finite.mem_allFin, nonroot])
          have regionSource :=
            compiled.fresh_region_source fresh
          have freshGet :
              attachment.fragmentRegions.get fresh = region :=
            DenseList.get_index _ _ _
          rw [freshGet] at regionSource
          rw [data] at regionSource
          have regionExact :
              attachment.fragmentRegion region =
                attachment.freshRegion fresh := by
            simp [ConcreteSpliceAttachment.fragmentRegion, nonroot, fresh]
          rw [regionExact, ConcreteDiagram.climb, regionSource]
          simp only [mapRegion]
          exact fragmentClimb_to_root compiled steps parent parentClimbed

private theorem fragmentRegion_injective
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    Function.Injective attachment.fragmentRegion := by
  intro left right same
  by_cases leftRoot : left = fragment.val.diagram.root
  · subst left
    have rightRoot :=
      (compiled.fragmentRegion_eq_site_iff right).mp
        (by simpa [ConcreteSpliceAttachment.fragmentRegion] using same.symm)
    exact rightRoot.symm
  · by_cases rightRoot : right = fragment.val.diagram.root
    · subst right
      have leftRoot' :=
        (compiled.fragmentRegion_eq_site_iff left).mp
          (by simpa [ConcreteSpliceAttachment.fragmentRegion] using same)
      exact (leftRoot leftRoot').elim
    · unfold ConcreteSpliceAttachment.fragmentRegion at same
      simp only [leftRoot, rightRoot, ↓reduceDIte] at same
      have indices :
          DenseList.index attachment.fragmentRegions left (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, leftRoot]) =
            DenseList.index attachment.fragmentRegions right (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, rightRoot]) := by
        apply Fin.ext
        simpa [ConcreteSpliceAttachment.freshRegion] using
          congrArg Fin.val same
      calc
        left = attachment.fragmentRegions.get
            (DenseList.index attachment.fragmentRegions left (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, leftRoot])) :=
          (DenseList.get_index _ _ _).symm
        _ = attachment.fragmentRegions.get
            (DenseList.index attachment.fragmentRegions right (by
              simp [ConcreteSpliceAttachment.fragmentRegions,
                ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, rightRoot])) :=
          congrArg attachment.fragmentRegions.get indices
        _ = right := DenseList.get_index _ _ _

private theorem generatedSiteContext_host_mem
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visible : compiled.site.frame.visible = outer.extend site)
    (wire : base.val.WireId)
    (member : wire ∈ compiled.site.frame.visible.ids) :
    attachment.hostWire wire ∈
      (generatedSiteContext attachment outer).ids := by
  rw [visible] at member
  change wire ∈ base.val.wiresAt site ++ outer.ids at member
  unfold generatedSiteContext ConcreteElaboration.WireContext.extend
  change attachment.hostWire wire ∈
    attachment.diagram.wiresAt (attachment.hostRegion site) ++
      (hostContext attachment outer).ids
  rcases List.mem_append.mp member with localMember | inherited
  · apply List.mem_append_left
    rw [compiled.site_wires]
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨wire, localMember, rfl⟩)
  · apply List.mem_append_right
    change attachment.hostWire wire ∈ outer.ids.map attachment.hostWire
    exact List.mem_map.mpr ⟨wire, inherited, rfl⟩

private theorem generatedSiteContext_covers
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visible : compiled.site.frame.visible = outer.extend site) :
    (generatedSiteContext attachment outer).Covers
      (attachment.hostRegion site) := by
  intro wire encloses
  have allocated : wire ∈ Data.Finite.allFin attachment.wireCount :=
    Data.Finite.mem_allFin wire
  rw [compiled.wire_allocations] at allocated
  rcases List.mem_append.mp allocated with host | fresh
  · rcases List.mem_map.mp host with ⟨sourceWire, _, rfl⟩
    rw [(compiled.host_wire_source sourceWire).2] at encloses
    have sourceEncloses :
        base.val.Encloses (base.val.wires sourceWire).scope site :=
      (hostEncloses_iff compiled _ _).mp encloses
    exact generatedSiteContext_host_mem compiled outer visible sourceWire
      (compiled.site.visible_of_encloses sourceWire sourceEncloses)
  · rcases List.mem_map.mp fresh with ⟨freshWire, _, rfl⟩
    let sourceWire := attachment.fragmentInternalWires.get freshWire
    have rootReach :=
      of_decide_eq_true
        ((List.all_eq_true.mp
          fragment.property.diagram.all_regions_reach_root)
          (fragment.val.diagram.wires sourceWire).scope
          (Data.Finite.mem_allFin _))
    obtain ⟨steps, rootClimb⟩ :=
      (ConcreteElaboration.encloses_iff_exists fragment.val.diagram
        fragment.val.diagram.root
        (fragment.val.diagram.wires sourceWire).scope).mp rootReach
    have siteEncloses :
        attachment.diagram.Encloses (attachment.hostRegion site)
          (attachment.fragmentRegion
            (fragment.val.diagram.wires sourceWire).scope) :=
      by
        have mappedClimb :=
          fragmentClimb_to_root compiled steps.val _ rootClimb
        have bounded :=
          successfulClimb_le_count definitions attachment.diagram
            compiled.generated_wellFormed steps.val
            (attachment.fragmentRegion
              (fragment.val.diagram.wires sourceWire).scope)
            (attachment.hostRegion site) mappedClimb
        apply
          (ConcreteElaboration.encloses_iff_exists attachment.diagram
            (attachment.hostRegion site)
            (attachment.fragmentRegion
              (fragment.val.diagram.wires sourceWire).scope)).mpr
        exact ⟨⟨steps.val, by omega⟩, mappedClimb⟩
    rw [(compiled.fresh_wire_source freshWire).2] at encloses
    have sameScope :=
      checked_encloses_antisymm definitions attachment.diagram
        compiled.generated_wellFormed encloses siteEncloses
    have targetScope :
        (attachment.diagram.wires
          (attachment.freshWire freshWire)).scope =
          attachment.hostRegion site :=
      (compiled.fresh_wire_source freshWire).2.trans sameScope
    change attachment.freshWire freshWire ∈
      (generatedSiteContext attachment outer).ids
    unfold generatedSiteContext ConcreteElaboration.WireContext.extend
    apply List.mem_append_left
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by
      simpa only [beq_iff_eq] using targetScope⟩

/--
Compile the grouped identity nodes introduced at the generated site from the
retained insertion receipt. This uses the retained site's visibility
projection and performs no site or region compiler search.
-/
theorem generatedIdentityNodes_compile
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visible : compiled.site.frame.visible = outer.extend site) :
    ∃ items :
        ItemSeq definitions (generatedSiteContext attachment outer).sigs,
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          ((Data.Finite.allFin attachment.identityRequests.length).map
            attachment.identityNode) =
        some items := by
  apply ConcreteElaboration.compileNodes?_complete definitions
    attachment.diagram compiled.generated_wellFormed
    (generatedSiteContext attachment outer) (attachment.hostRegion site)
    (generatedSiteContext_covers compiled outer visible)
  intro node member
  rcases List.mem_map.mp member with ⟨identity, _, rfl⟩
  rw [compiled.identity_node]
  rfl

private theorem compileNodes_append
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (left ++ right) =
      (do
        let leftItems ←
          ConcreteElaboration.compileNodes? definitions diagram context left
        let rightItems ←
          ConcreteElaboration.compileNodes? definitions diagram context right
        pure (leftItems.append rightItems)) := by
  induction left with
  | nil => simp [ConcreteElaboration.compileNodes?, ItemSeq.append]
  | cons head tail induction =>
      simp only [List.cons_append, ConcreteElaboration.compileNodes?]
      rw [induction]
      simp [Option.bind_assoc, ItemSeq.append]

private theorem compileChildren_append
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.RegionId) :
    ConcreteElaboration.compileChildrenWith? definitions diagram recurse
        context (left ++ right) =
      (do
        let leftItems ←
          ConcreteElaboration.compileChildrenWith? definitions diagram
            recurse context left
        let rightItems ←
          ConcreteElaboration.compileChildrenWith? definitions diagram
            recurse context right
        pure (leftItems.append rightItems)) := by
  induction left with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?, ItemSeq.append]
  | cons head tail induction =>
      simp only [List.cons_append,
        ConcreteElaboration.compileChildrenWith?]
      rw [induction]
      simp [Option.bind_assoc, ItemSeq.append]

theorem compileRegion_fuel_mono
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :
    ∀ (sourceFuel targetFuel : Nat),
      sourceFuel ≤ targetFuel →
      ∀ (region : diagram.RegionId)
        (context : ConcreteElaboration.WireContext diagram)
        {body : Region definitions context.sigs},
        ConcreteElaboration.compileRegion? definitions diagram sourceFuel
            region context =
          some body →
        ConcreteElaboration.compileRegion? definitions diagram targetFuel
            region context =
          some body := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro targetFuel fuelLe region context body sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ childFuel induction =>
      intro targetFuel fuelLe region context body sourceCompiled
      obtain ⟨extra, targetFuelEquation⟩ :=
        Nat.exists_eq_add_of_le fuelLe
      subst targetFuel
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
      obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
        Option.bind_eq_some_iff.mp sourceCompiled
      obtain ⟨sourceChildren, sourceChildrenCompiled,
          sourceAfterChildren⟩ :=
        Option.bind_eq_some_iff.mp sourceAfterNodes
      have bodyShape := Option.some.inj sourceAfterChildren
      subst body
      have childFuelLe : childFuel ≤ childFuel + extra := by omega
      have childrenCompiled :
          ConcreteElaboration.compileChildrenWith? definitions diagram
              (ConcreteElaboration.compileRegion? definitions diagram
                (childFuel + extra))
              (context.extend region) (diagram.childrenOf region) =
            some sourceChildren := by
        let extended := context.extend region
        generalize childrenEquation :
            diagram.childrenOf region = children
        rw [childrenEquation] at sourceChildrenCompiled
        clear sourceCompiled sourceAfterNodes sourceAfterChildren
          childrenEquation
        induction children generalizing sourceChildren with
        | nil =>
            simpa [ConcreteElaboration.compileChildrenWith?] using
              sourceChildrenCompiled
        | cons child tail childrenInduction =>
            obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
                sourceTailCompiled, sourceChildrenShape⟩ :=
              compileChildren_cons_components definitions diagram
                (ConcreteElaboration.compileRegion? definitions diagram
                  childFuel)
                extended child tail sourceChildren sourceChildrenCompiled
            subst sourceChildren
            have targetHeadCompiled :=
              induction (childFuel + extra) childFuelLe child extended
                sourceHeadCompiled
            have targetTailCompiled :=
              childrenInduction sourceTail sourceTailCompiled
            dsimp [extended] at targetHeadCompiled
            simp only [ConcreteElaboration.compileChildrenWith?]
            rw [targetHeadCompiled, targetTailCompiled]
            rfl
      have targetFuelShape :
          childFuel + 1 + extra = childFuel + extra + 1 := by omega
      rw [targetFuelShape]
      simp only [ConcreteElaboration.compileRegion?]
      rw [sourceNodesCompiled, childrenCompiled]
      rfl

private theorem compileChildren_fuel_mono
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (sourceFuel targetFuel : Nat)
    (fuelLe : sourceFuel ≤ targetFuel)
    (context : ConcreteElaboration.WireContext diagram) :
    ∀ (children : List diagram.RegionId)
      {items : ItemSeq definitions context.sigs},
      ConcreteElaboration.compileChildrenWith? definitions diagram
          (ConcreteElaboration.compileRegion? definitions diagram sourceFuel)
          context children =
        some items →
      ConcreteElaboration.compileChildrenWith? definitions diagram
          (ConcreteElaboration.compileRegion? definitions diagram targetFuel)
          context children =
        some items := by
  intro children
  induction children with
  | nil =>
      intro items compiled
      simpa [ConcreteElaboration.compileChildrenWith?] using compiled
  | cons child tail induction =>
      intro items compiled
      obtain ⟨head, rest, headCompiled, restCompiled, itemsShape⟩ :=
        compileChildren_cons_components definitions diagram
          (ConcreteElaboration.compileRegion? definitions diagram sourceFuel)
          context child tail items compiled
      subst items
      have targetHeadCompiled :=
        compileRegion_fuel_mono definitions diagram sourceFuel targetFuel
          fuelLe child context headCompiled
      have targetRestCompiled := induction restCompiled
      simp [ConcreteElaboration.compileChildrenWith?, targetHeadCompiled,
        targetRestCompiled]

set_option maxHeartbeats 800000 in
private theorem fragmentRegion_compile
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (fuel : Nat)
      (region : fragment.val.diagram.RegionId)
      (nonroot : region ≠ fragment.val.diagram.root)
      (sourceContext :
        ConcreteElaboration.WireContext fragment.val.diagram)
      (targetContext :
        ConcreteElaboration.WireContext attachment.diagram)
      (rho : WireRenaming sourceContext.sigs targetContext.sigs)
      (contextAction :
        ∀ {sig} (value : Var sourceContext.sigs sig),
          ConcreteElaboration.WireContext.origin attachment.diagram
              targetContext.ids (rho value) =
            attachment.fragmentWire
              (ConcreteElaboration.WireContext.origin
                fragment.val.diagram sourceContext.ids value))
      (targetAbove :
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.fragmentRegion region))
      {sourceBody : Region definitions sourceContext.sigs},
      ConcreteElaboration.compileRegion? definitions fragment.val.diagram
          fuel region sourceContext =
        some sourceBody →
      ∃ targetBody : Region definitions targetContext.sigs,
        ConcreteElaboration.compileRegion? definitions attachment.diagram
            fuel (attachment.fragmentRegion region) targetContext =
          some targetBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro region nonroot sourceContext targetContext rho contextAction
        targetAbove sourceBody sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ childFuel induction =>
      intro region nonroot sourceContext targetContext rho contextAction
        targetAbove sourceBody sourceCompiled
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
      obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
        Option.bind_eq_some_iff.mp sourceCompiled
      obtain ⟨sourceChildren, sourceChildrenCompiled,
          sourceAfterChildren⟩ :=
        Option.bind_eq_some_iff.mp sourceAfterNodes
      have sourceBodyShape := Option.some.inj sourceAfterChildren
      subst sourceBody
      let extendedRho :
          WireRenaming
            (sourceContext.extend region).sigs
            (targetContext.extend
              (attachment.fragmentRegion region)).sigs :=
        fragmentExtendedRenaming compiled region nonroot
          sourceContext targetContext rho contextAction
      have targetExtendedNodup :
          (targetContext.extend
            (attachment.fragmentRegion region)).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions attachment.diagram
          compiled.generated_wellFormed targetContext
          (attachment.fragmentRegion region) targetAbove
      obtain ⟨targetNodes, targetNodesCompiled, _⟩ :=
        copiedFragmentNodes_natural compiled
          (sourceContext.extend region)
          (targetContext.extend (attachment.fragmentRegion region))
          targetExtendedNodup extendedRho
          (fragmentExtendedRenaming_contextAction compiled region nonroot
            sourceContext targetContext rho contextAction)
          (fragment.val.diagram.nodesAt region) sourceNodesCompiled
      have childrenNonroot :
          ∀ child,
            child ∈ fragment.val.diagram.childrenOf region →
              child ≠ fragment.val.diagram.root := by
        intro child member root
        have childData :=
          ConcreteElaboration.mem_childrenOf fragment.val.diagram
            region child member
        subst child
        rw [fragment.property.diagram.root_is_sheet] at childData
        contradiction
      have generateChildren :
          ∀ (children : List fragment.val.diagram.RegionId)
            (sourceItems :
              ItemSeq definitions (sourceContext.extend region).sigs),
            (∀ child, child ∈ children →
              child ∈ fragment.val.diagram.childrenOf region) →
            ConcreteElaboration.compileChildrenWith? definitions
                fragment.val.diagram
                (ConcreteElaboration.compileRegion? definitions
                  fragment.val.diagram childFuel)
                (sourceContext.extend region) children =
              some sourceItems →
            ∃ targetItems :
                ItemSeq definitions
                  (targetContext.extend
                    (attachment.fragmentRegion region)).sigs,
              ConcreteElaboration.compileChildrenWith? definitions
                  attachment.diagram
                  (ConcreteElaboration.compileRegion? definitions
                    attachment.diagram childFuel)
                  (targetContext.extend
                    (attachment.fragmentRegion region))
                  (children.map attachment.fragmentRegion) =
                some targetItems := by
        intro children
        induction children with
        | nil =>
            intro sourceItems members sourceCompiled
            have sourceExact : sourceItems = .nil := by
              simpa [ConcreteElaboration.compileChildrenWith?] using
                (Option.some.inj sourceCompiled).symm
            subst sourceItems
            exact ⟨.nil, rfl⟩
        | cons child tail tailInduction =>
            intro sourceItems members sourceCompiled
            have childMember :
                child ∈ fragment.val.diagram.childrenOf region :=
              members child (by simp)
            obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
                sourceTailCompiled, sourceItemsShape⟩ :=
              compileChildren_cons_components definitions
                fragment.val.diagram
                (ConcreteElaboration.compileRegion? definitions
                  fragment.val.diagram childFuel)
                (sourceContext.extend region) child tail sourceItems
                sourceCompiled
            obtain ⟨targetHead, targetHeadCompiled⟩ :=
              induction child (childrenNonroot child childMember)
                (sourceContext.extend region)
                (targetContext.extend (attachment.fragmentRegion region))
                extendedRho
                (fragmentExtendedRenaming_contextAction compiled region
                  nonroot sourceContext targetContext rho contextAction)
                (by
                  have targetMember :
                      attachment.fragmentRegion child ∈
                        attachment.diagram.childrenOf
                          (attachment.fragmentRegion region) := by
                    rw [compiled.fragment_children region nonroot]
                    exact List.mem_map.mpr ⟨child, childMember, rfl⟩
                  exact
                    ConcreteElaboration.extend_above_child definitions
                      attachment.diagram compiled.generated_wellFormed
                      targetContext (attachment.fragmentRegion region)
                      (attachment.fragmentRegion child) targetAbove
                      (ConcreteElaboration.mem_childrenOf
                        attachment.diagram
                        (attachment.fragmentRegion region)
                        (attachment.fragmentRegion child) targetMember))
                sourceHeadCompiled
            obtain ⟨targetTail, targetTailCompiled⟩ :=
              tailInduction sourceTail (by
                intro candidate member
                exact members candidate (by simp [member]))
                sourceTailCompiled
            refine ⟨.cons (.cut targetHead) targetTail, ?_⟩
            simp [ConcreteElaboration.compileChildrenWith?,
              targetHeadCompiled, targetTailCompiled]
      obtain ⟨targetChildren, targetChildrenCompiled⟩ :=
        generateChildren (fragment.val.diagram.childrenOf region)
          sourceChildren (fun child member => member) sourceChildrenCompiled
      let targetBody :
          Region definitions targetContext.sigs :=
        ConcreteElaboration.finishRegion attachment.diagram targetContext
          (attachment.fragmentRegion region)
          (.mk (targetNodes.append targetChildren))
      refine ⟨targetBody, ?_⟩
      simp only [ConcreteElaboration.compileRegion?]
      rw [compiled.fragment_nodes region nonroot,
        compiled.fragment_children region nonroot]
      change
        (ConcreteElaboration.compileNodes? definitions attachment.diagram
          (targetContext.extend (attachment.fragmentRegion region))
          ((fragment.val.diagram.nodesAt region).map
            attachment.fragmentNode)).bind (fun nodes =>
          (ConcreteElaboration.compileChildrenWith? definitions
            attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram childFuel)
            (targetContext.extend (attachment.fragmentRegion region))
            ((fragment.val.diagram.childrenOf region).map
              attachment.fragmentRegion)).bind (fun children =>
              some
                (ConcreteElaboration.finishRegion attachment.diagram
                  targetContext (attachment.fragmentRegion region)
                  (.mk (nodes.append children))))) =
          some targetBody
      rw [targetNodesCompiled, targetChildrenCompiled]
      rfl

set_option maxHeartbeats 800000 in
private theorem hostRegion_compile_outside
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (fuel : Nat)
      (region : base.val.RegionId)
      (outside : ¬base.val.Encloses region site)
      (sourceContext : ConcreteElaboration.WireContext base.val)
      (targetContext :
        ConcreteElaboration.WireContext attachment.diagram)
      (rho : WireRenaming sourceContext.sigs targetContext.sigs)
      (contextAction :
        ∀ {sig} (value : Var sourceContext.sigs sig),
          ConcreteElaboration.WireContext.origin attachment.diagram
              targetContext.ids (rho value) =
            attachment.hostWire
              (ConcreteElaboration.WireContext.origin
                base.val sourceContext.ids value))
      (targetAbove :
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion region))
      {sourceBody : Region definitions sourceContext.sigs},
      ConcreteElaboration.compileRegion? definitions base.val fuel region
          sourceContext =
        some sourceBody →
      ∃ targetBody : Region definitions targetContext.sigs,
        ConcreteElaboration.compileRegion? definitions attachment.diagram
            fuel (attachment.hostRegion region) targetContext =
          some targetBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outside sourceContext targetContext rho contextAction
        targetAbove sourceBody sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ childFuel induction =>
      intro region outside sourceContext targetContext rho contextAction
        targetAbove sourceBody sourceCompiled
      have notSite : region ≠ site :=
        fun same => outside (same ▸ ConcreteDiagram.encloses_refl base.val site)
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled
      obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
        Option.bind_eq_some_iff.mp sourceCompiled
      obtain ⟨sourceChildren, sourceChildrenCompiled,
          sourceAfterChildren⟩ :=
        Option.bind_eq_some_iff.mp sourceAfterNodes
      have sourceBodyShape := Option.some.inj sourceAfterChildren
      subst sourceBody
      let extendedRho :
          WireRenaming
            (sourceContext.extend region).sigs
            (targetContext.extend (attachment.hostRegion region)).sigs :=
        hostExtendedRenaming compiled region notSite
          sourceContext targetContext rho contextAction
      have targetExtendedNodup :
          (targetContext.extend
            (attachment.hostRegion region)).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions attachment.diagram
          compiled.generated_wellFormed targetContext
          (attachment.hostRegion region) targetAbove
      obtain ⟨targetNodes, targetNodesCompiled, _⟩ :=
        copiedHostNodes_natural compiled
          (sourceContext.extend region)
          (targetContext.extend (attachment.hostRegion region))
          targetExtendedNodup extendedRho
          (hostExtendedRenaming_contextAction compiled region notSite
            sourceContext targetContext rho contextAction)
          (base.val.nodesAt region) sourceNodesCompiled
      have childrenOutside :
          ∀ child, child ∈ base.val.childrenOf region →
            ¬base.val.Encloses child site := by
        intro child member childSite
        have childData :=
          ConcreteElaboration.mem_childrenOf base.val region child member
        exact outside
          (encloses_trans definitions base.val base.property
            (parent_encloses_child base.val child region childData)
            childSite)
      have generateChildren :
          ∀ (children : List base.val.RegionId)
            (sourceItems :
              ItemSeq definitions (sourceContext.extend region).sigs),
            (∀ child, child ∈ children →
              child ∈ base.val.childrenOf region) →
            ConcreteElaboration.compileChildrenWith? definitions base.val
                (ConcreteElaboration.compileRegion? definitions base.val
                  childFuel)
                (sourceContext.extend region) children =
              some sourceItems →
            ∃ targetItems :
                ItemSeq definitions
                  (targetContext.extend
                    (attachment.hostRegion region)).sigs,
              ConcreteElaboration.compileChildrenWith? definitions
                  attachment.diagram
                  (ConcreteElaboration.compileRegion? definitions
                    attachment.diagram childFuel)
                  (targetContext.extend (attachment.hostRegion region))
                  (children.map attachment.hostRegion) =
                some targetItems := by
        intro children
        induction children with
        | nil =>
            intro sourceItems members sourceCompiled
            have sourceExact : sourceItems = .nil :=
              (Option.some.inj sourceCompiled).symm
            subst sourceItems
            exact ⟨.nil, rfl⟩
        | cons child tail tailInduction =>
            intro sourceItems members sourceCompiled
            have childMember : child ∈ base.val.childrenOf region :=
              members child (by simp)
            obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
                sourceTailCompiled, sourceItemsShape⟩ :=
              compileChildren_cons_components definitions base.val
                (ConcreteElaboration.compileRegion? definitions base.val
                  childFuel)
                (sourceContext.extend region) child tail sourceItems
                sourceCompiled
            have targetMember :
                attachment.hostRegion child ∈
                  attachment.diagram.childrenOf
                    (attachment.hostRegion region) := by
              rw [hostChildren_offsite compiled region notSite]
              exact List.mem_map.mpr ⟨child, childMember, rfl⟩
            obtain ⟨targetHead, targetHeadCompiled⟩ :=
              induction child (childrenOutside child childMember)
                (sourceContext.extend region)
                (targetContext.extend (attachment.hostRegion region))
                extendedRho
                (hostExtendedRenaming_contextAction compiled region notSite
                  sourceContext targetContext rho contextAction)
                (ConcreteElaboration.extend_above_child definitions
                  attachment.diagram compiled.generated_wellFormed
                  targetContext (attachment.hostRegion region)
                  (attachment.hostRegion child) targetAbove
                  (ConcreteElaboration.mem_childrenOf attachment.diagram
                    (attachment.hostRegion region)
                    (attachment.hostRegion child) targetMember))
                sourceHeadCompiled
            obtain ⟨targetTail, targetTailCompiled⟩ :=
              tailInduction sourceTail (by
                intro candidate member
                exact members candidate (by simp [member]))
                sourceTailCompiled
            refine ⟨.cons (.cut targetHead) targetTail, ?_⟩
            simp [ConcreteElaboration.compileChildrenWith?,
              targetHeadCompiled, targetTailCompiled]
      obtain ⟨targetChildren, targetChildrenCompiled⟩ :=
        generateChildren (base.val.childrenOf region) sourceChildren
          (fun child member => member) sourceChildrenCompiled
      let targetBody : Region definitions targetContext.sigs :=
        ConcreteElaboration.finishRegion attachment.diagram targetContext
          (attachment.hostRegion region)
          (.mk (targetNodes.append targetChildren))
      refine ⟨targetBody, ?_⟩
      simp only [ConcreteElaboration.compileRegion?]
      rw [hostNodes_offsite compiled region notSite,
        hostChildren_offsite compiled region notSite]
      change
        (ConcreteElaboration.compileNodes? definitions attachment.diagram
          (targetContext.extend (attachment.hostRegion region))
          ((base.val.nodesAt region).map attachment.hostNode)).bind
            (fun nodes =>
          (ConcreteElaboration.compileChildrenWith? definitions
            attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram childFuel)
            (targetContext.extend (attachment.hostRegion region))
            ((base.val.childrenOf region).map
              attachment.hostRegion)).bind (fun children =>
              some
                (ConcreteElaboration.finishRegion attachment.diagram
                  targetContext (attachment.hostRegion region)
                  (.mk (nodes.append children))))) =
          some targetBody
      rw [targetNodesCompiled, targetChildrenCompiled]
      rfl

set_option maxHeartbeats 1200000 in
theorem generatedSiteBody_compile
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (sourceFuelLe : sourceFuel ≤ targetFuel)
    (fragmentFuel : fragment.val.diagram.regionCount ≤ targetFuel)
    (outer : ConcreteElaboration.WireContext base.val)
    (visible : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    {sourceBody : Region definitions (outer.extend site).sigs}
    (sourceCompiled :
      compileRegionBody? definitions base.val sourceFuel site outer =
        some sourceBody) :
    ∃ targetBody :
        Region definitions (generatedSiteContext attachment outer).sigs,
      compileRegionBody? definitions attachment.diagram targetFuel
          (attachment.hostRegion site) (hostContext attachment outer) =
        some targetBody := by
  unfold compileRegionBody? at sourceCompiled ⊢
  obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
    Option.bind_eq_some_iff.mp sourceCompiled
  obtain ⟨sourceChildren, sourceChildrenCompiled, sourceAfterChildren⟩ :=
    Option.bind_eq_some_iff.mp sourceAfterNodes
  let hostRho :
      WireRenaming (outer.extend site).sigs
        (generatedSiteContext attachment outer).sigs :=
    generatedSiteHostRenaming compiled outer
  let fragmentRho :
      WireRenaming (fragmentRootContext fragment).sigs
        (generatedSiteContext attachment outer).sigs :=
    generatedSiteFragmentRenaming compiled outer visible
  have generatedNodup :=
    generatedSiteContext_nodup compiled outer targetAbove
  obtain ⟨targetHostNodes, targetHostNodesCompiled, _⟩ :=
    copiedHostNodes_natural compiled (outer.extend site)
      (generatedSiteContext attachment outer) generatedNodup hostRho
      (generatedSiteHostRenaming_contextAction compiled outer)
      (base.val.nodesAt site) sourceNodesCompiled
  obtain ⟨sourceFragmentNodes, sourceFragmentChildren,
      sourceFragmentNodesCompiled, sourceFragmentChildrenCompiled⟩ :=
    openRoot_compile_components fragmentCompiled
  obtain ⟨targetFragmentNodes, targetFragmentNodesCompiled, _⟩ :=
    copiedFragmentNodes_natural compiled
      (fragmentRootContext fragment)
      (generatedSiteContext attachment outer) generatedNodup fragmentRho
      (generatedSiteFragmentRenaming_contextAction compiled outer visible)
      (fragment.val.diagram.nodesAt fragment.val.diagram.root)
      sourceFragmentNodesCompiled
  obtain ⟨identityItems, identityItemsCompiled⟩ :=
    generatedIdentityNodes_compile compiled outer visible
  have generateHostChildren :
      ∀ (children : List base.val.RegionId)
        (sourceItems : ItemSeq definitions (outer.extend site).sigs),
        (∀ child, child ∈ children →
          child ∈ base.val.childrenOf site) →
        ConcreteElaboration.compileChildrenWith? definitions base.val
            (ConcreteElaboration.compileRegion? definitions base.val
              sourceFuel)
            (outer.extend site) children =
          some sourceItems →
        ∃ targetItems :
            ItemSeq definitions
              (generatedSiteContext attachment outer).sigs,
          ConcreteElaboration.compileChildrenWith? definitions
              attachment.diagram
              (ConcreteElaboration.compileRegion? definitions
                attachment.diagram targetFuel)
              (generatedSiteContext attachment outer)
              (children.map attachment.hostRegion) =
            some targetItems := by
    intro children
    induction children with
    | nil =>
        intro sourceItems members generated
        have exactItems : sourceItems = .nil :=
          (Option.some.inj generated).symm
        subst sourceItems
        exact ⟨.nil, rfl⟩
    | cons child tail induction =>
        intro sourceItems members generated
        have childMember : child ∈ base.val.childrenOf site :=
          members child (by simp)
        obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
            sourceTailCompiled, sourceItemsShape⟩ :=
          compileChildren_cons_components definitions base.val
            (ConcreteElaboration.compileRegion? definitions base.val
              sourceFuel)
            (outer.extend site) child tail sourceItems generated
        have childData :=
          ConcreteElaboration.mem_childrenOf base.val site child childMember
        have childOutside : ¬base.val.Encloses child site := by
          intro childSite
          have siteChild :=
            parent_encloses_child base.val child site childData
          have same :=
            checked_encloses_antisymm definitions base.val base.property
              siteChild childSite
          exact
            (checked_child_ne_parent definitions base.val base.property
              child site childData) same.symm
        have targetMember :
            attachment.hostRegion child ∈
              attachment.diagram.childrenOf (attachment.hostRegion site) := by
          rw [compiled.site_children]
          exact List.mem_append_left _
            (List.mem_map.mpr ⟨child, childMember, rfl⟩)
        obtain ⟨targetHead, targetHeadCompiled⟩ :=
          hostRegion_compile_outside compiled targetFuel child childOutside
            (outer.extend site) (generatedSiteContext attachment outer)
            hostRho
            (generatedSiteHostRenaming_contextAction compiled outer)
            (ConcreteElaboration.extend_above_child definitions
              attachment.diagram compiled.generated_wellFormed
              (hostContext attachment outer) (attachment.hostRegion site)
              (attachment.hostRegion child) targetAbove
              (ConcreteElaboration.mem_childrenOf attachment.diagram
                (attachment.hostRegion site)
                (attachment.hostRegion child) targetMember))
            (compileRegion_fuel_mono definitions base.val sourceFuel
              targetFuel sourceFuelLe child (outer.extend site)
              sourceHeadCompiled)
        obtain ⟨targetTail, targetTailCompiled⟩ :=
          induction sourceTail (by
            intro candidate member
            exact members candidate (by simp [member]))
            sourceTailCompiled
        refine ⟨.cons (.cut targetHead) targetTail, ?_⟩
        simp [ConcreteElaboration.compileChildrenWith?,
          targetHeadCompiled, targetTailCompiled]
  obtain ⟨targetHostChildren, targetHostChildrenCompiled⟩ :=
    generateHostChildren (base.val.childrenOf site) sourceChildren
      (fun child member => member) sourceChildrenCompiled
  have fragmentChildrenNonroot :
      ∀ child,
        child ∈ fragment.val.diagram.childrenOf fragment.val.diagram.root →
          child ≠ fragment.val.diagram.root := by
    intro child member root
    have childData :=
      ConcreteElaboration.mem_childrenOf fragment.val.diagram
        fragment.val.diagram.root child member
    subst child
    rw [fragment.property.diagram.root_is_sheet] at childData
    contradiction
  have generateFragmentChildren :
      ∀ (children : List fragment.val.diagram.RegionId)
        (sourceItems :
          ItemSeq definitions (fragmentRootContext fragment).sigs),
        (∀ child, child ∈ children →
          child ∈ fragment.val.diagram.childrenOf
            fragment.val.diagram.root) →
        ConcreteElaboration.compileChildrenWith? definitions
            fragment.val.diagram
            (ConcreteElaboration.compileRegion? definitions
              fragment.val.diagram targetFuel)
            (fragmentRootContext fragment) children =
          some sourceItems →
        ∃ targetItems :
            ItemSeq definitions
              (generatedSiteContext attachment outer).sigs,
          ConcreteElaboration.compileChildrenWith? definitions
              attachment.diagram
              (ConcreteElaboration.compileRegion? definitions
                attachment.diagram targetFuel)
              (generatedSiteContext attachment outer)
              (children.map attachment.fragmentRegion) =
            some targetItems := by
    intro children
    induction children with
    | nil =>
        intro sourceItems members generated
        have exactItems : sourceItems = .nil :=
          (Option.some.inj generated).symm
        subst sourceItems
        exact ⟨.nil, rfl⟩
    | cons child tail induction =>
        intro sourceItems members generated
        have childMember :
            child ∈ fragment.val.diagram.childrenOf
              fragment.val.diagram.root :=
          members child (by simp)
        obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
            sourceTailCompiled, sourceItemsShape⟩ :=
          compileChildren_cons_components definitions
            fragment.val.diagram
            (ConcreteElaboration.compileRegion? definitions
              fragment.val.diagram targetFuel)
            (fragmentRootContext fragment) child tail sourceItems generated
        have targetMember :
            attachment.fragmentRegion child ∈
              attachment.diagram.childrenOf
                (attachment.hostRegion site) := by
          rw [compiled.site_children]
          exact List.mem_append_right _
            (List.mem_map.mpr ⟨child, childMember, rfl⟩)
        obtain ⟨targetHead, targetHeadCompiled⟩ :=
          fragmentRegion_compile compiled targetFuel child
            (fragmentChildrenNonroot child childMember)
            (fragmentRootContext fragment)
            (generatedSiteContext attachment outer) fragmentRho
            (generatedSiteFragmentRenaming_contextAction
              compiled outer visible)
            (ConcreteElaboration.extend_above_child definitions
              attachment.diagram compiled.generated_wellFormed
              (hostContext attachment outer) (attachment.hostRegion site)
              (attachment.fragmentRegion child) targetAbove
              (ConcreteElaboration.mem_childrenOf attachment.diagram
                (attachment.hostRegion site)
                (attachment.fragmentRegion child) targetMember))
            sourceHeadCompiled
        obtain ⟨targetTail, targetTailCompiled⟩ :=
          induction sourceTail (by
            intro candidate member
            exact members candidate (by simp [member]))
            sourceTailCompiled
        refine ⟨.cons (.cut targetHead) targetTail, ?_⟩
        simp [ConcreteElaboration.compileChildrenWith?,
          targetHeadCompiled, targetTailCompiled]
  obtain ⟨targetFragmentChildren, targetFragmentChildrenCompiled⟩ :=
    generateFragmentChildren
      (fragment.val.diagram.childrenOf fragment.val.diagram.root)
      sourceFragmentChildren (fun child member => member)
      (compileChildren_fuel_mono definitions fragment.val.diagram
        fragment.val.diagram.regionCount targetFuel fragmentFuel
        (fragmentRootContext fragment)
        (fragment.val.diagram.childrenOf fragment.val.diagram.root)
        sourceFragmentChildrenCompiled)
  let targetNodes :=
    (targetHostNodes.append targetFragmentNodes).append identityItems
  let targetChildren :=
    targetHostChildren.append targetFragmentChildren
  have targetCopiedNodesCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          ((base.val.nodesAt site).map attachment.hostNode ++
            (fragment.val.diagram.nodesAt
              fragment.val.diagram.root).map attachment.fragmentNode) =
        some (targetHostNodes.append targetFragmentNodes) := by
    calc
      _ = (do
          let leftItems ← ConcreteElaboration.compileNodes? definitions
            attachment.diagram (generatedSiteContext attachment outer)
            ((base.val.nodesAt site).map attachment.hostNode)
          let rightItems ← ConcreteElaboration.compileNodes? definitions
            attachment.diagram (generatedSiteContext attachment outer)
            ((fragment.val.diagram.nodesAt
              fragment.val.diagram.root).map attachment.fragmentNode)
          pure (leftItems.append rightItems)) :=
        compileNodes_append definitions attachment.diagram
          (generatedSiteContext attachment outer)
          ((base.val.nodesAt site).map attachment.hostNode)
          ((fragment.val.diagram.nodesAt
            fragment.val.diagram.root).map attachment.fragmentNode)
      _ = _ := by
        simp [targetHostNodesCompiled, targetFragmentNodesCompiled]
  have targetNodesCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          (((base.val.nodesAt site).map attachment.hostNode ++
            (fragment.val.diagram.nodesAt
              fragment.val.diagram.root).map attachment.fragmentNode) ++
            (Data.Finite.allFin attachment.identityRequests.length).map
              attachment.identityNode) =
        some targetNodes := by
    calc
      _ = (do
          let leftItems ← ConcreteElaboration.compileNodes? definitions
            attachment.diagram (generatedSiteContext attachment outer)
            ((base.val.nodesAt site).map attachment.hostNode ++
              (fragment.val.diagram.nodesAt
                fragment.val.diagram.root).map attachment.fragmentNode)
          let rightItems ← ConcreteElaboration.compileNodes? definitions
            attachment.diagram (generatedSiteContext attachment outer)
            ((Data.Finite.allFin attachment.identityRequests.length).map
              attachment.identityNode)
          pure (leftItems.append rightItems)) :=
        compileNodes_append definitions attachment.diagram
          (generatedSiteContext attachment outer)
          ((base.val.nodesAt site).map attachment.hostNode ++
            (fragment.val.diagram.nodesAt
              fragment.val.diagram.root).map attachment.fragmentNode)
          ((Data.Finite.allFin attachment.identityRequests.length).map
            attachment.identityNode)
      _ = _ := by
        simp [targetCopiedNodesCompiled, identityItemsCompiled, targetNodes]
  have targetChildrenCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram targetFuel)
          (generatedSiteContext attachment outer)
          ((base.val.childrenOf site).map attachment.hostRegion ++
            (fragment.val.diagram.childrenOf
              fragment.val.diagram.root).map attachment.fragmentRegion) =
        some targetChildren := by
    calc
      _ = (do
          let leftItems ←
            ConcreteElaboration.compileChildrenWith? definitions
              attachment.diagram
              (ConcreteElaboration.compileRegion? definitions
                attachment.diagram targetFuel)
              (generatedSiteContext attachment outer)
              ((base.val.childrenOf site).map attachment.hostRegion)
          let rightItems ←
            ConcreteElaboration.compileChildrenWith? definitions
              attachment.diagram
              (ConcreteElaboration.compileRegion? definitions
                attachment.diagram targetFuel)
              (generatedSiteContext attachment outer)
              ((fragment.val.diagram.childrenOf
                fragment.val.diagram.root).map attachment.fragmentRegion)
          pure (leftItems.append rightItems)) :=
        compileChildren_append definitions attachment.diagram
          (ConcreteElaboration.compileRegion? definitions attachment.diagram
            targetFuel)
          (generatedSiteContext attachment outer)
          ((base.val.childrenOf site).map attachment.hostRegion)
          ((fragment.val.diagram.childrenOf
            fragment.val.diagram.root).map attachment.fragmentRegion)
      _ = _ := by
        simp [targetHostChildrenCompiled, targetFragmentChildrenCompiled,
          targetChildren]
  let targetBody : Region definitions
      (generatedSiteContext attachment outer).sigs :=
    .mk (targetNodes.append targetChildren)
  refine ⟨targetBody, ?_⟩
  change
    (ConcreteElaboration.compileNodes? definitions attachment.diagram
      (generatedSiteContext attachment outer)
      (attachment.diagram.nodesAt (attachment.hostRegion site))).bind
        (fun nodes =>
      (ConcreteElaboration.compileChildrenWith? definitions
        attachment.diagram
        (ConcreteElaboration.compileRegion? definitions attachment.diagram
          targetFuel)
        (generatedSiteContext attachment outer)
        (attachment.diagram.childrenOf
          (attachment.hostRegion site))).bind (fun children =>
            some (.mk (nodes.append children)))) =
      some targetBody
  rw [compiled.site_nodes, compiled.site_children,
    targetNodesCompiled, targetChildrenCompiled]
  rfl

private theorem hostChildren_compile_outside
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (fuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              sourceContext.ids value)) :
    ∀ (children : List base.val.RegionId),
      (∀ child, child ∈ children → ¬base.val.Encloses child site) →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion child)) →
      ∀ {sourceItems : ItemSeq definitions sourceContext.sigs},
        ConcreteElaboration.compileChildrenWith? definitions base.val
            (ConcreteElaboration.compileRegion? definitions base.val fuel)
            sourceContext children =
          some sourceItems →
        ∃ targetItems : ItemSeq definitions targetContext.sigs,
          ConcreteElaboration.compileChildrenWith? definitions
              attachment.diagram
              (ConcreteElaboration.compileRegion? definitions
                attachment.diagram fuel)
              targetContext (children.map attachment.hostRegion) =
            some targetItems := by
  intro children
  induction children with
  | nil =>
      intro outside above sourceItems sourceCompiled
      have sourceExact : sourceItems = .nil :=
        (Option.some.inj sourceCompiled).symm
      subst sourceItems
      exact ⟨.nil, rfl⟩
  | cons child tail induction =>
      intro outside above sourceItems sourceCompiled
      obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
          sourceTailCompiled, sourceItemsShape⟩ :=
        compileChildren_cons_components definitions base.val
          (ConcreteElaboration.compileRegion? definitions base.val fuel)
          sourceContext child tail sourceItems sourceCompiled
      obtain ⟨targetHead, targetHeadCompiled⟩ :=
        hostRegion_compile_outside compiled fuel child
          (outside child (by simp)) sourceContext targetContext rho
          contextAction (above child (by simp)) sourceHeadCompiled
      obtain ⟨targetTail, targetTailCompiled⟩ :=
        induction
          (by
            intro candidate member
            exact outside candidate (by simp [member]))
          (by
            intro candidate member
            exact above candidate (by simp [member]))
          sourceTailCompiled
      refine ⟨.cons (.cut targetHead) targetTail, ?_⟩
      simp [ConcreteElaboration.compileChildrenWith?, targetHeadCompiled,
        targetTailCompiled]

/--
Recursive authority for one source-driven host sibling branch. The selected
child and every skipped outside sibling are retained while the target frame is
generated, so compilation and semantics fold the same receipt.
-/
inductive GeneratedSiblingProvenance
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (selected : base.val.RegionId)
    (sourceNested :
      RegionFrame definitions base.val sourceContext)
    (targetNested :
      RegionFrame definitions attachment.diagram targetContext) :
    ItemSeq definitions sourceContext.sigs →
    ItemSeq definitions targetContext.sigs →
    List base.val.RegionId →
    RegionFrame definitions base.val sourceContext →
    RegionFrame definitions attachment.diagram targetContext →
    Prop where
  | selected
      (sourceLeading : ItemSeq definitions sourceContext.sigs)
      (targetLeading :
        ItemSeq definitions targetContext.sigs)
      (tail : List base.val.RegionId)
      (sourceSuffix : ItemSeq definitions sourceContext.sigs)
      (targetSuffix :
        ItemSeq definitions targetContext.sigs)
      (sourceSuffixCompiled :
        ConcreteElaboration.compileChildrenWith? definitions base.val
            (ConcreteElaboration.compileRegion? definitions base.val
              sourceFuel)
            sourceContext tail =
          some sourceSuffix)
      (targetSuffixCompiled :
        ConcreteElaboration.compileChildrenWith? definitions
            attachment.diagram
            (ConcreteElaboration.compileRegion? definitions
              attachment.diagram targetFuel)
            targetContext
            (tail.map attachment.hostRegion) =
          some targetSuffix) :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading targetLeading
        (selected :: tail)
        { visible := sourceNested.visible
          siteBody := sourceNested.siteBody
          context := .surround sourceLeading (.cut sourceNested.context)
            sourceSuffix }
        { visible := targetNested.visible
          siteBody := targetNested.siteBody
          context := .surround targetLeading (.cut targetNested.context)
            targetSuffix }
  | outside
      (sourceLeading : ItemSeq definitions sourceContext.sigs)
      (targetLeading :
        ItemSeq definitions targetContext.sigs)
      (child : base.val.RegionId)
      (tail : List base.val.RegionId)
      (different : child ≠ selected)
      (sourceBody : Region definitions sourceContext.sigs)
      (targetBody :
        Region definitions targetContext.sigs)
      (sourceBodyCompiled :
        ConcreteElaboration.compileRegion? definitions base.val sourceFuel
            child sourceContext =
          some sourceBody)
      (targetBodyCompiled :
        ConcreteElaboration.compileRegion? definitions attachment.diagram
            targetFuel (attachment.hostRegion child)
            targetContext =
          some targetBody)
      {sourceFrame :
        RegionFrame definitions base.val sourceContext}
      {targetFrame :
        RegionFrame definitions attachment.diagram targetContext}
      (rest :
        GeneratedSiblingProvenance compiled sourceFuel targetFuel
          sourceContext targetContext selected sourceNested targetNested
          (sourceLeading.append (.cons (.cut sourceBody) .nil))
          (targetLeading.append (.cons (.cut targetBody) .nil))
          tail sourceFrame targetFrame) :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading targetLeading
        (child :: tail) sourceFrame targetFrame

theorem compileHostSiblingFrame
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (fuelLe : sourceFuel ≤ targetFuel)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              sourceContext.ids value))
    (selected : base.val.RegionId)
    (sourceNested : RegionFrame definitions base.val sourceContext)
    (targetNested :
      RegionFrame definitions attachment.diagram targetContext)
    (sourceLeading : ItemSeq definitions sourceContext.sigs)
    (targetLeading : ItemSeq definitions targetContext.sigs) :
    ∀ (children : List base.val.RegionId),
      children.Nodup →
      (∀ child, child ∈ children → child ≠ selected →
        ¬base.val.Encloses child site) →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion child)) →
      ∀ {sourceFrame : RegionFrame definitions base.val sourceContext},
        compileSiblingFrame? definitions base.val sourceFuel sourceContext
            selected sourceNested sourceLeading children =
          some sourceFrame →
        ∃ targetFrame :
            RegionFrame definitions attachment.diagram targetContext,
          compileSiblingFrame? definitions attachment.diagram targetFuel
              targetContext (attachment.hostRegion selected) targetNested
              targetLeading (children.map attachment.hostRegion) =
            some targetFrame ∧
          targetFrame.visible = targetNested.visible ∧
          GeneratedSiblingProvenance compiled sourceFuel targetFuel
            sourceContext targetContext selected sourceNested targetNested sourceLeading
            targetLeading children sourceFrame targetFrame := by
  intro children
  induction children generalizing sourceLeading targetLeading with
  | nil =>
      intro nodup outside above sourceFrame sourceCompiled
      simp [compileSiblingFrame?] at sourceCompiled
  | cons child tail induction =>
      intro nodup outside above sourceFrame sourceCompiled
      rw [List.nodup_cons] at nodup
      unfold compileSiblingFrame? at sourceCompiled ⊢
      by_cases same : child = selected
      · subst child
        simp only [↓reduceDIte] at sourceCompiled
        obtain ⟨sourceSuffix, sourceSuffixCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        have sourceFrameExact :
            ({ visible := sourceNested.visible
               siteBody := sourceNested.siteBody
               context := .surround sourceLeading
                 (.cut sourceNested.context) sourceSuffix } :
              RegionFrame definitions base.val sourceContext) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        subst sourceFrame
        have sourceSuffixAtTargetFuel :=
          compileChildren_fuel_mono definitions base.val sourceFuel
            targetFuel fuelLe sourceContext tail sourceSuffixCompiled
        obtain ⟨targetSuffix, targetSuffixCompiled⟩ :=
          hostChildren_compile_outside compiled targetFuel sourceContext
            targetContext rho contextAction tail
            (by
              intro candidate member
              apply outside candidate (by simp [member])
              intro equality
              subst candidate
              exact nodup.1 member)
            (by
              intro candidate member
              exact above candidate (by simp [member]))
            sourceSuffixAtTargetFuel
        let targetFrame :
            RegionFrame definitions attachment.diagram targetContext :=
          { visible := targetNested.visible
            siteBody := targetNested.siteBody
            context := .surround targetLeading
              (.cut targetNested.context) targetSuffix }
        refine ⟨targetFrame, ?_, rfl, ?_⟩
        simp only [List.map_cons, compileSiblingFrame?]
        simp [targetSuffixCompiled, targetFrame]
        exact
          .selected sourceLeading targetLeading tail sourceSuffix
            targetSuffix sourceSuffixCompiled targetSuffixCompiled
      · simp only [same, ↓reduceDIte] at sourceCompiled
        obtain ⟨sourceHead, sourceHeadCompiled, sourceRecursive⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        have sourceHeadAtTargetFuel :=
          compileRegion_fuel_mono definitions base.val sourceFuel targetFuel
            fuelLe child sourceContext sourceHeadCompiled
        obtain ⟨targetHead, targetHeadCompiled⟩ :=
          hostRegion_compile_outside compiled targetFuel child
            (outside child (by simp) same) sourceContext targetContext rho
            contextAction (above child (by simp)) sourceHeadAtTargetFuel
        obtain ⟨targetFrame, targetCompiled, targetVisible, provenance⟩ :=
          induction
            (sourceLeading.append (.cons (.cut sourceHead) .nil))
            (targetLeading.append (.cons (.cut targetHead) .nil))
            nodup.2
            (by
              intro candidate member different
              exact outside candidate (by simp [member]) different)
            (by
              intro candidate member
              exact above candidate (by simp [member]))
            sourceRecursive
        have targetDifferent :
            attachment.hostRegion child ≠
              attachment.hostRegion selected := by
          intro equality
          exact same (hostRegion_injective attachment equality)
        refine ⟨targetFrame, ?_, targetVisible, ?_⟩
        simp only [List.map_cons, compileSiblingFrame?]
        split
        · rename_i equality
          exact (targetDifferent equality).elim
        · rw [targetHeadCompiled]
          exact targetCompiled
        · exact
            .outside sourceLeading targetLeading child tail same sourceHead
              targetHead sourceHeadCompiled targetHeadCompiled provenance

/-- The accepted source sibling equation is a provenance fold. -/
theorem GeneratedSiblingProvenance.sourceGenerated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {selected : base.val.RegionId}
    {sourceNested :
      RegionFrame definitions base.val sourceContext}
    {targetNested :
      RegionFrame definitions attachment.diagram targetContext}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {targetLeading :
      ItemSeq definitions targetContext.sigs}
    {children : List base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceContext}
    {targetFrame :
      RegionFrame definitions attachment.diagram targetContext}
    (provenance :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading targetLeading
        children sourceFrame targetFrame) :
    compileSiblingFrame? definitions base.val sourceFuel sourceContext
        selected sourceNested sourceLeading children =
      some sourceFrame := by
  induction provenance with
  | selected sourceLeading targetLeading tail sourceSuffix targetSuffix
      sourceSuffixCompiled targetSuffixCompiled =>
      simp [compileSiblingFrame?, sourceSuffixCompiled]
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      simp [compileSiblingFrame?, different, sourceBodyCompiled, induction]

/-- Generated sibling compilation is a fold over the same provenance. -/
theorem GeneratedSiblingProvenance.targetGenerated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {selected : base.val.RegionId}
    {sourceNested :
      RegionFrame definitions base.val sourceContext}
    {targetNested :
      RegionFrame definitions attachment.diagram targetContext}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {targetLeading :
      ItemSeq definitions targetContext.sigs}
    {children : List base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceContext}
    {targetFrame :
      RegionFrame definitions attachment.diagram targetContext}
    (provenance :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading targetLeading
        children sourceFrame targetFrame) :
    compileSiblingFrame? definitions attachment.diagram targetFuel
        targetContext
        (attachment.hostRegion selected) targetNested targetLeading
        (children.map attachment.hostRegion) =
      some targetFrame := by
  induction provenance with
  | selected sourceLeading targetLeading tail sourceSuffix targetSuffix
      sourceSuffixCompiled targetSuffixCompiled =>
      simp [compileSiblingFrame?, targetSuffixCompiled]
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      have mappedDifferent :
          attachment.hostRegion child ≠ attachment.hostRegion selected :=
        fun same => different (hostRegion_injective attachment same)
      simp only [List.map_cons, compileSiblingFrame?]
      split
      · rename_i same
        exact (mappedDifferent same).elim
      · rw [targetBodyCompiled]
        exact induction

/-- Both sibling endpoints retain the selected nested visible contexts. -/
theorem GeneratedSiblingProvenance.visible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {selected : base.val.RegionId}
    {sourceNested :
      RegionFrame definitions base.val sourceContext}
    {targetNested :
      RegionFrame definitions attachment.diagram targetContext}
    {sourceLeading : ItemSeq definitions sourceContext.sigs}
    {targetLeading :
      ItemSeq definitions targetContext.sigs}
    {children : List base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceContext}
    {targetFrame :
      RegionFrame definitions attachment.diagram targetContext}
    (provenance :
      GeneratedSiblingProvenance compiled sourceFuel targetFuel sourceContext
        targetContext selected sourceNested targetNested sourceLeading targetLeading
        children sourceFrame targetFrame) :
    sourceFrame.visible = sourceNested.visible ∧
      targetFrame.visible = targetNested.visible := by
  induction provenance with
  | selected => exact ⟨rfl, rfl⟩
  | outside sourceLeading targetLeading child tail different sourceBody
      targetBody sourceBodyCompiled targetBodyCompiled rest induction =>
      exact induction

private theorem map_nodup
    {α β : Type} (map : α → β) (injective : Function.Injective map) :
    ∀ {items : List α}, items.Nodup → (items.map map).Nodup
  | [], _ => by simp
  | head :: tail, nodup => by
      rw [List.nodup_cons] at nodup
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨by
        intro member
        obtain ⟨candidate, candidateMember, same⟩ :=
          List.mem_map.mp member
        exact nodup.1 ((injective same.symm) ▸ candidateMember),
        map_nodup map injective nodup.2⟩

theorem hostContext_above
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (context : ConcreteElaboration.WireContext base.val)
    (region : base.val.RegionId)
    (above : ConcreteElaboration.ContextAbove base.val context region) :
    ConcreteElaboration.ContextAbove attachment.diagram
      (hostContext attachment context) (attachment.hostRegion region) := by
  constructor
  · exact map_nodup attachment.hostWire attachment.hostWire_injective above.1
  · intro wire member
    obtain ⟨sourceWire, sourceMember, wireExact⟩ :=
      List.mem_map.mp member
    subst wire
    obtain ⟨steps, positive, climbed⟩ :=
      above.2 sourceWire sourceMember
    refine ⟨steps, positive, ?_⟩
    rw [hostClimb compiled, climbed]
    simp [ConcreteSpliceAttachment.diagram_wire_hostWire_scope]
    rfl

theorem findHostEnclosing
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (children : List base.val.RegionId),
      ((children.map attachment.hostRegion).find? fun candidate =>
          decide
            (attachment.diagram.Encloses candidate
              (attachment.hostRegion site))) =
        (children.find? fun candidate =>
          decide (base.val.Encloses candidate site)).map
            attachment.hostRegion
  | [] => rfl
  | child :: tail => by
      simp only [List.map_cons, List.find?_cons]
      by_cases encloses : base.val.Encloses child site
      · have targetEncloses :=
          (hostEncloses_iff compiled child site).2 encloses
        simp [List.find?, decide_eq_true targetEncloses,
          decide_eq_true encloses]
        rfl
      · have targetOutside :
            ¬attachment.diagram.Encloses
              (attachment.hostRegion child) (attachment.hostRegion site) :=
          fun target =>
            encloses ((hostEncloses_iff compiled child site).1 target)
        simp [List.find?, decide_eq_false targetOutside,
          decide_eq_false encloses, findHostEnclosing compiled tail]

/-- Reindex an item sequence along equality of its wire context. -/
def rebaseItemSeq
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (items : ItemSeq definitions left.sigs) :
    ItemSeq definitions right.sigs := by
  subst right
  exact items

/-- Reindex a frame along equality of its outer wire context. -/
def rebaseRegionFrame
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    RegionFrame definitions diagram right := by
  subst right
  exact frame

@[simp] theorem rebaseRegionFrame_visible
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (frame : RegionFrame definitions diagram left) :
    (rebaseRegionFrame same frame).visible = frame.visible := by
  subst right
  rfl

theorem compileFrameBranch_cast_context
    (diagram : ConcreteDiagram definitions.length)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (site : diagram.RegionId)
    (fuel : Nat)
    (selected : diagram.RegionId)
    (nodes : List diagram.NodeId)
    (children : List diagram.RegionId)
    {leading : ItemSeq definitions left.sigs}
    {nested frame : RegionFrame definitions diagram left}
    (leadingCompiled :
      ConcreteElaboration.compileNodes? definitions diagram left nodes =
        some leading)
    (nestedCompiled :
      compileRegionFrame? definitions diagram site fuel selected left =
        some nested)
    (frameCompiled :
      compileSiblingFrame? definitions diagram fuel left selected nested
          leading children =
        some frame) :
    ∃ (rightLeading : ItemSeq definitions right.sigs)
      (rightNested rightFrame : RegionFrame definitions diagram right),
      ConcreteElaboration.compileNodes? definitions diagram right nodes =
          some rightLeading ∧
      compileRegionFrame? definitions diagram site fuel selected right =
          some rightNested ∧
      compileSiblingFrame? definitions diagram fuel right selected
          rightNested rightLeading children =
          some rightFrame ∧
      rightFrame.visible = frame.visible ∧
      rightLeading = rebaseItemSeq same leading ∧
      rightNested = rebaseRegionFrame same nested ∧
      rightFrame = rebaseRegionFrame same frame := by
  subst right
  exact
    ⟨leading, nested, frame, leadingCompiled, nestedCompiled,
      frameCompiled, rfl, rfl, rfl, rfl⟩

/--
The single recursive provenance authority for source-driven insertion frames.
The site constructor owns the generated leaf. Each ancestor owns the paired
sibling branch and retains the nested provenance rather than erasing it to
endpoint compiler equations.
-/
inductive GeneratedFrameProvenance
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    (sourceFuel : Nat) →
    (sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val) →
    (region : base.val.RegionId) →
    RegionFrame definitions base.val sourceOuter →
    RegionFrame definitions attachment.diagram
      (hostContext attachment sourceOuter) →
    Prop where
  | site
      (childFuel : Nat)
      (sourceOuter : ConcreteElaboration.WireContext base.val)
      (sourceBody :
        Region definitions (sourceOuter.extend site).sigs)
      (targetBody :
        Region definitions (generatedSiteContext attachment sourceOuter).sigs)
      (sourceAbove :
        ConcreteElaboration.ContextAbove base.val sourceOuter site)
      (siteVisible :
        compiled.site.frame.visible = sourceOuter.extend site)
      (sourceBodyCompiled :
        compileRegionBody? definitions base.val childFuel site sourceOuter =
          some sourceBody)
      (targetBodyCompiled :
        compileRegionBody? definitions attachment.diagram
            (childFuel + fragment.val.diagram.regionCount)
            (attachment.hostRegion site)
            (hostContext attachment sourceOuter) =
          some targetBody) :
      GeneratedFrameProvenance compiled (childFuel + 1)
        sourceOuter sourceOuter site
        { visible := sourceOuter.extend site
          siteBody := sourceBody
          context := bindContextFor base.val sourceOuter.ids
            (base.val.wiresAt site) .hole }
        { visible := generatedSiteContext attachment sourceOuter
          siteBody := targetBody
          context := bindContextFor attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt (attachment.hostRegion site))
            .hole }
  | ancestor
      (childFuel : Nat)
      (sourceOuter siteOuter :
        ConcreteElaboration.WireContext base.val)
      (region selected : base.val.RegionId)
      (notSite : region ≠ site)
      (sourceAbove :
        ConcreteElaboration.ContextAbove base.val sourceOuter region)
      (sourceNodes :
        ItemSeq definitions (sourceOuter.extend region).sigs)
      (targetNodes :
        ItemSeq definitions
          (hostContext attachment (sourceOuter.extend region)).sigs)
      (sourceNested :
        RegionFrame definitions base.val (sourceOuter.extend region))
      (targetNested :
        RegionFrame definitions attachment.diagram
          (hostContext attachment (sourceOuter.extend region)))
      (sourceAround :
        RegionFrame definitions base.val (sourceOuter.extend region))
      (targetAround :
        RegionFrame definitions attachment.diagram
          (hostContext attachment (sourceOuter.extend region)))
      (sourceNodesCompiled :
        ConcreteElaboration.compileNodes? definitions base.val
            (sourceOuter.extend region) (base.val.nodesAt region) =
          some sourceNodes)
      (targetNodesCompiled :
        ConcreteElaboration.compileNodes? definitions attachment.diagram
            (hostContext attachment (sourceOuter.extend region))
            ((base.val.nodesAt region).map attachment.hostNode) =
          some targetNodes)
      (selectedFound :
        (base.val.childrenOf region).find?
            (fun candidate => decide (base.val.Encloses candidate site)) =
          some selected)
      (sourceNestedCompiled :
        compileRegionFrame? definitions base.val site childFuel selected
            (sourceOuter.extend region) =
          some sourceNested)
      (siblings :
        GeneratedSiblingProvenance compiled childFuel
          (childFuel + fragment.val.diagram.regionCount)
          (sourceOuter.extend region)
          (hostContext attachment (sourceOuter.extend region)) selected
          sourceNested targetNested sourceNodes targetNodes
          (base.val.childrenOf region) sourceAround targetAround)
      (childrenNodup : (base.val.childrenOf region).Nodup)
      (otherOutside :
        ∀ child, child ∈ base.val.childrenOf region →
          child ≠ selected → ¬base.val.Encloses child site)
      (allChildrenAbove :
        ∀ child, child ∈ base.val.childrenOf region →
          ConcreteElaboration.ContextAbove attachment.diagram
            (hostContext attachment (sourceOuter.extend region))
            (attachment.hostRegion child))
      (nested :
        GeneratedFrameProvenance compiled childFuel
          (sourceOuter.extend region) siteOuter selected sourceNested
          targetNested) :
      GeneratedFrameProvenance compiled (childFuel + 1)
        sourceOuter siteOuter region
        { visible := sourceAround.visible
          siteBody := sourceAround.siteBody
          context := bindContextFor base.val sourceOuter.ids
            (base.val.wiresAt region) sourceAround.context }
        { visible :=
            (rebaseRegionFrame
              (hostContext_extend_offsite compiled sourceOuter region
                notSite)
              targetAround).visible
          siteBody :=
            (rebaseRegionFrame
              (hostContext_extend_offsite compiled sourceOuter region
                notSite)
              targetAround).siteBody
          context := bindContextFor attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt
              (attachment.hostRegion region))
            (rebaseRegionFrame
            (hostContext_extend_offsite compiled sourceOuter region
                notSite)
              targetAround).context }

/-- Target-frame compilation is a fold over the recursive provenance. -/
theorem GeneratedFrameProvenance.targetGenerated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (provenance :
      GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
        region sourceFrame targetFrame) :
    compileRegionFrame? definitions attachment.diagram
        (attachment.hostRegion site)
        (sourceFuel + fragment.val.diagram.regionCount)
        (attachment.hostRegion region)
        (hostContext attachment sourceOuter) =
      some targetFrame := by
  induction provenance with
  | site childFuel sourceOuter sourceBody targetBody sourceAbove siteVisible
      sourceBodyCompiled targetBodyCompiled =>
      have fuelShape :
          childFuel + 1 + fragment.val.diagram.regionCount =
            childFuel + fragment.val.diagram.regionCount + 1 := by
        omega
      rw [fuelShape]
      simp only [compileRegionFrame?, ↓reduceDIte]
      rw [targetBodyCompiled]
      rfl
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested induction =>
      have contextEquality :=
        hostContext_extend_offsite compiled sourceOuter region notSite
      have targetAroundCompiled := siblings.targetGenerated
      obtain ⟨targetNodes', targetNested', targetAround',
          targetNodesCompiled', targetNestedCompiled',
          targetAroundCompiled', _, targetNodesExact, targetNestedExact,
          targetAroundExact⟩ :=
        compileFrameBranch_cast_context attachment.diagram contextEquality
          (attachment.hostRegion site)
          (childFuel + fragment.val.diagram.regionCount)
          (attachment.hostRegion selected)
          ((base.val.nodesAt region).map attachment.hostNode)
          ((base.val.childrenOf region).map attachment.hostRegion)
          targetNodesCompiled induction targetAroundCompiled
      subst targetNodes'
      subst targetNested'
      subst targetAround'
      let targetNodes' := rebaseItemSeq contextEquality targetNodes
      let targetNested' := rebaseRegionFrame contextEquality targetNested
      let targetAround' := rebaseRegionFrame contextEquality targetAround
      let targetFrame' :
          RegionFrame definitions attachment.diagram
            (hostContext attachment sourceOuter) :=
        { visible := targetAround'.visible
          siteBody := targetAround'.siteBody
          context := bindContextFor attachment.diagram
            (hostContext attachment sourceOuter).ids
            (attachment.diagram.wiresAt
              (attachment.hostRegion region))
            targetAround'.context }
      change
        compileRegionFrame? definitions attachment.diagram
            (attachment.hostRegion site)
            (childFuel + 1 + fragment.val.diagram.regionCount)
            (attachment.hostRegion region)
            (hostContext attachment sourceOuter) =
          some targetFrame'
      have targetNotAtSite :
          attachment.hostRegion region ≠ attachment.hostRegion site :=
        fun same => notSite (hostRegion_injective attachment same)
      have fuelShape :
          childFuel + 1 + fragment.val.diagram.regionCount =
            childFuel + fragment.val.diagram.regionCount + 1 := by
        omega
      rw [fuelShape]
      simp only [compileRegionFrame?]
      split
      · rename_i same
        exact (targetNotAtSite same).elim
      · rw [hostNodes_offsite compiled region notSite]
        change
          (ConcreteElaboration.compileNodes? definitions attachment.diagram
            ((hostContext attachment sourceOuter).extend
              (attachment.hostRegion region))
            ((base.val.nodesAt region).map attachment.hostNode)).bind
              (fun nodes =>
                ((attachment.diagram.childrenOf
                  (attachment.hostRegion region)).find? fun candidate =>
                    decide
                      (attachment.diagram.Encloses candidate
                        (attachment.hostRegion site))).bind (fun child =>
                  (compileRegionFrame? definitions attachment.diagram
                    (attachment.hostRegion site)
                    (childFuel + fragment.val.diagram.regionCount) child
                    ((hostContext attachment sourceOuter).extend
                      (attachment.hostRegion region))).bind (fun nested =>
                    (compileSiblingFrame? definitions attachment.diagram
                      (childFuel + fragment.val.diagram.regionCount)
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region))
                      child nested nodes
                      (attachment.diagram.childrenOf
                        (attachment.hostRegion region))).bind (fun around =>
                        some
                          { visible := around.visible
                            siteBody := around.siteBody
                            context := bindContextFor attachment.diagram
                              (hostContext attachment sourceOuter).ids
                              (attachment.diagram.wiresAt
                                (attachment.hostRegion region))
                              around.context })))) =
            some targetFrame'
        rw [targetNodesCompiled']
        rw [hostChildren_offsite compiled region notSite]
        rw [findHostEnclosing compiled, selectedFound]
        change
          (compileRegionFrame? definitions attachment.diagram
            (attachment.hostRegion site)
            (childFuel + fragment.val.diagram.regionCount)
            (attachment.hostRegion selected)
            ((hostContext attachment sourceOuter).extend
              (attachment.hostRegion region))).bind (fun nested =>
              (compileSiblingFrame? definitions attachment.diagram
                (childFuel + fragment.val.diagram.regionCount)
                ((hostContext attachment sourceOuter).extend
                  (attachment.hostRegion region))
                (attachment.hostRegion selected) nested targetNodes'
                ((base.val.childrenOf region).map
                  attachment.hostRegion)).bind (fun around =>
                    some
                      { visible := around.visible
                        siteBody := around.siteBody
                        context := bindContextFor attachment.diagram
                          (hostContext attachment sourceOuter).ids
                          (attachment.diagram.wiresAt
                            (attachment.hostRegion region))
                          around.context })) =
            some targetFrame'
        rw [targetNestedCompiled']
        change
          (compileSiblingFrame? definitions attachment.diagram
            (childFuel + fragment.val.diagram.regionCount)
            ((hostContext attachment sourceOuter).extend
              (attachment.hostRegion region))
            (attachment.hostRegion selected) targetNested' targetNodes'
            ((base.val.childrenOf region).map
              attachment.hostRegion)).bind (fun around =>
                some
                  { visible := around.visible
                    siteBody := around.siteBody
                    context := bindContextFor attachment.diagram
                      (hostContext attachment sourceOuter).ids
                      (attachment.diagram.wiresAt
                        (attachment.hostRegion region))
                      around.context }) =
            some targetFrame'
        rw [targetAroundCompiled']
        rfl

/-- The generated visible context is also derived from provenance. -/
theorem GeneratedFrameProvenance.targetVisible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel : Nat}
    {sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val}
    {region : base.val.RegionId}
    {sourceFrame : RegionFrame definitions base.val sourceOuter}
    {targetFrame :
      RegionFrame definitions attachment.diagram
        (hostContext attachment sourceOuter)}
    (provenance :
      GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
        region sourceFrame targetFrame) :
    targetFrame.visible = generatedSiteContext attachment siteOuter := by
  induction provenance with
  | site => rfl
  | ancestor childFuel sourceOuter siteOuter region selected notSite
      sourceAbove sourceNodes targetNodes sourceNested targetNested
      sourceAround targetAround sourceNodesCompiled targetNodesCompiled
      selectedFound sourceNestedCompiled siblings childrenNodup otherOutside
      allChildrenAbove nested induction =>
      have aroundVisible := siblings.visible.2
      change
        (rebaseRegionFrame
          (hostContext_extend_offsite compiled sourceOuter region notSite)
          targetAround).visible =
            generatedSiteContext attachment siteOuter
      exact
        (rebaseRegionFrame_visible
          (hostContext_extend_offsite compiled sourceOuter region notSite)
          targetAround).trans (aroundVisible.trans induction)

set_option maxHeartbeats 1600000 in
private theorem compileRegionFrame_generate
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ∀ (sourceFuel : Nat)
      (sourceOuter : ConcreteElaboration.WireContext base.val)
      (region : base.val.RegionId)
      (sourceAbove :
        ConcreteElaboration.ContextAbove base.val sourceOuter region)
      (siteOuter : ConcreteElaboration.WireContext base.val)
      (siteVisible :
        compiled.site.frame.visible = siteOuter.extend site)
      {sourceFrame : RegionFrame definitions base.val sourceOuter},
      sourceFrame.visible = siteOuter.extend site →
      compileRegionFrame? definitions base.val site sourceFuel region
          sourceOuter =
        some sourceFrame →
      ∃ targetFrame :
          RegionFrame definitions attachment.diagram
            (hostContext attachment sourceOuter),
        compileRegionFrame? definitions attachment.diagram
            (attachment.hostRegion site)
            (sourceFuel + fragment.val.diagram.regionCount)
            (attachment.hostRegion region)
            (hostContext attachment sourceOuter) =
        some targetFrame ∧
        targetFrame.visible =
          generatedSiteContext attachment siteOuter ∧
        GeneratedFrameProvenance compiled sourceFuel sourceOuter siteOuter
          region sourceFrame targetFrame := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro sourceOuter region sourceAbove siteOuter siteVisible sourceFrame
        sourceVisible sourceCompiled
      simp [compileRegionFrame?] at sourceCompiled
  | succ sourceChildFuel induction =>
      intro sourceOuter region sourceAbove siteOuter siteVisible sourceFrame
        sourceVisible sourceCompiled
      by_cases atSite : region = site
      · subst region
        simp only [compileRegionFrame?, ↓reduceDIte] at sourceCompiled
        obtain ⟨sourceBody, sourceBodyCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        have sourceFrameExact :
            ({ visible := sourceOuter.extend site
               siteBody := sourceBody
               context := bindContextFor base.val sourceOuter.ids
                 (base.val.wiresAt site) .hole } :
              RegionFrame definitions base.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        subst sourceFrame
        have outerExact : sourceOuter = siteOuter := by
          have idsExact :
              (sourceOuter.extend site).ids =
                (siteOuter.extend site).ids :=
            congrArg ConcreteElaboration.WireContext.ids sourceVisible
          unfold ConcreteElaboration.WireContext.extend at idsExact
          have tails :=
            (List.append_right_inj (base.val.wiresAt site)).mp idsExact
          cases sourceOuter
          cases siteOuter
          simp_all
        subst siteOuter
        have visible :
            compiled.site.frame.visible = sourceOuter.extend site := by
          exact siteVisible
        obtain ⟨targetBody, targetBodyCompiled⟩ :=
          generatedSiteBody_compile compiled sourceChildFuel
            (sourceChildFuel + fragment.val.diagram.regionCount)
            (by omega) (by omega) sourceOuter visible
            (hostContext_above compiled sourceOuter site sourceAbove)
            sourceBodyCompiled
        let targetFrame :
            RegionFrame definitions attachment.diagram
              (hostContext attachment sourceOuter) :=
          { visible := generatedSiteContext attachment sourceOuter
            siteBody := targetBody
            context := bindContextFor attachment.diagram
              (hostContext attachment sourceOuter).ids
              (attachment.diagram.wiresAt (attachment.hostRegion site))
              .hole }
        refine ⟨targetFrame, ?_, rfl, ?_⟩
        · have fuelShape :
              sourceChildFuel + 1 + fragment.val.diagram.regionCount =
                sourceChildFuel + fragment.val.diagram.regionCount + 1 := by
            omega
          rw [fuelShape]
          simp only [compileRegionFrame?, ↓reduceDIte]
          rw [targetBodyCompiled]
          rfl
        · exact
            GeneratedFrameProvenance.site sourceChildFuel
              sourceOuter sourceBody targetBody sourceAbove visible
              sourceBodyCompiled targetBodyCompiled
      · simp only [compileRegionFrame?, atSite, ↓reduceDIte]
          at sourceCompiled
        obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨selected, selectedFound, sourceAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNodes
        obtain ⟨sourceNested, sourceNestedCompiled, sourceAfterNested⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterSelected
        obtain ⟨sourceAround, sourceAroundCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNested
        have sourceFrameExact :
            ({ visible := sourceAround.visible
               siteBody := sourceAround.siteBody
               context := bindContextFor base.val sourceOuter.ids
                 (base.val.wiresAt region) sourceAround.context } :
              RegionFrame definitions base.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        subst sourceFrame
        have aroundVisible :
            sourceAround.visible = sourceNested.visible :=
          siblingFrame_visible definitions base.val sourceChildFuel
            (sourceOuter.extend region) selected sourceNested sourceNodes
            (base.val.childrenOf region) sourceAroundCompiled
        have nestedSourceVisible :
            sourceNested.visible = siteOuter.extend site :=
          aroundVisible.symm.trans sourceVisible
        have selectedMember :=
          List.mem_of_find?_eq_some selectedFound
        have sourceSelectedAbove :=
          ConcreteElaboration.extend_above_child definitions base.val
            base.property sourceOuter region selected sourceAbove
            (ConcreteElaboration.mem_childrenOf base.val region selected
              selectedMember)
        obtain ⟨targetNested, targetNestedCompiled, targetNestedVisible,
            nestedProvenance⟩ :=
          induction (sourceOuter.extend region) selected sourceSelectedAbove
            siteOuter siteVisible nestedSourceVisible sourceNestedCompiled
        let extendedRho :
            WireRenaming (sourceOuter.extend region).sigs
              (hostContext attachment
                (sourceOuter.extend region)).sigs :=
          hostContextRenaming attachment (sourceOuter.extend region)
        have targetExtendedAbove :=
          hostContext_above compiled (sourceOuter.extend region) selected
            sourceSelectedAbove
        have targetNodup := targetExtendedAbove.1
        obtain ⟨targetNodes, targetNodesCompiled, _⟩ :=
          copiedHostNodes_natural compiled (sourceOuter.extend region)
            (hostContext attachment (sourceOuter.extend region))
            targetNodup extendedRho
            (hostContextRenaming_origin attachment
              (sourceOuter.extend region))
            (base.val.nodesAt region) sourceNodesCompiled
        have selectedEncloses :
            base.val.Encloses selected site :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate =>
                decide (base.val.Encloses candidate site)) selectedFound)
        have childrenNodup :
            (base.val.childrenOf region).Nodup := by
          unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
          exact
            (Data.Finite.allFin_nodup base.val.regionCount).filter _
        have otherOutside :
            ∀ child, child ∈ base.val.childrenOf region →
              child ≠ selected → ¬base.val.Encloses child site := by
          intro child member different childSite
          have childData :=
            ConcreteElaboration.mem_childrenOf base.val region child member
          have regionChild :=
            parent_encloses_child base.val child region childData
          have childStrict :=
            checked_child_ne_parent definitions base.val base.property
              child region childData
          have selectedData :=
            ConcreteElaboration.mem_childrenOf base.val region selected
              selectedMember
          have selectedChild :=
            selected_child_encloses_middle definitions base.val base.property
              regionChild childStrict selectedData selectedEncloses childSite
          rcases checked_encloses_child_split base.val selected child region
              childData selectedChild with same | selectedRegion
          · exact different same.symm
          · have regionSelected :=
              parent_encloses_child base.val selected region selectedData
            have same :=
              checked_encloses_antisymm definitions base.val base.property
                selectedRegion regionSelected
            exact
              (checked_child_ne_parent definitions base.val base.property
                selected region selectedData) same
        have allChildrenAbove :
            ∀ child, child ∈ base.val.childrenOf region →
              ConcreteElaboration.ContextAbove attachment.diagram
                (hostContext attachment (sourceOuter.extend region))
                (attachment.hostRegion child) := by
          intro child member
          exact hostContext_above compiled (sourceOuter.extend region) child
            (ConcreteElaboration.extend_above_child definitions base.val
              base.property sourceOuter region child sourceAbove
              (ConcreteElaboration.mem_childrenOf base.val region child
                member))
        obtain ⟨targetAround, targetAroundCompiled, targetAroundVisible,
            siblingProvenance⟩ :=
          compileHostSiblingFrame compiled sourceChildFuel
            (sourceChildFuel + fragment.val.diagram.regionCount)
            (by omega) (sourceOuter.extend region)
            (hostContext attachment (sourceOuter.extend region))
            extendedRho
            (hostContextRenaming_origin attachment
              (sourceOuter.extend region))
            selected sourceNested targetNested sourceNodes targetNodes
            (base.val.childrenOf region) childrenNodup otherOutside
            allChildrenAbove sourceAroundCompiled
        have contextEquality :=
          hostContext_extend_offsite compiled sourceOuter region atSite
        obtain ⟨targetNodes', targetNested', targetAround',
            targetNodesCompiled', targetNestedCompiled',
            targetAroundCompiled', targetAroundVisible',
            targetNodesExact, targetNestedExact, targetAroundExact⟩ :=
          compileFrameBranch_cast_context attachment.diagram contextEquality
            (attachment.hostRegion site)
            (sourceChildFuel + fragment.val.diagram.regionCount)
            (attachment.hostRegion selected)
            ((base.val.nodesAt region).map attachment.hostNode)
            ((base.val.childrenOf region).map attachment.hostRegion)
            targetNodesCompiled targetNestedCompiled targetAroundCompiled
        subst targetNodes'
        subst targetNested'
        subst targetAround'
        let targetNodes' := rebaseItemSeq contextEquality targetNodes
        let targetNested' := rebaseRegionFrame contextEquality targetNested
        let targetAround' := rebaseRegionFrame contextEquality targetAround
        let targetFrame :
            RegionFrame definitions attachment.diagram
              (hostContext attachment sourceOuter) :=
          { visible := targetAround'.visible
            siteBody := targetAround'.siteBody
            context := bindContextFor attachment.diagram
              (hostContext attachment sourceOuter).ids
              (attachment.diagram.wiresAt
                (attachment.hostRegion region))
              targetAround'.context }
        have targetNotAtSite :
            attachment.hostRegion region ≠
              attachment.hostRegion site :=
          fun same => atSite (hostRegion_injective attachment same)
        refine ⟨targetFrame, ?_, ?_, ?_⟩
        · have fuelShape :
              sourceChildFuel + 1 + fragment.val.diagram.regionCount =
                sourceChildFuel + fragment.val.diagram.regionCount + 1 := by
            omega
          rw [fuelShape]
          simp only [compileRegionFrame?]
          split
          · rename_i same
            exact (targetNotAtSite same).elim
          · rw [hostNodes_offsite compiled region atSite]
            change
              (ConcreteElaboration.compileNodes? definitions
                attachment.diagram
                ((hostContext attachment sourceOuter).extend
                  (attachment.hostRegion region))
                ((base.val.nodesAt region).map
                  attachment.hostNode)).bind (fun nodes =>
                ((attachment.diagram.childrenOf
                  (attachment.hostRegion region)).find? fun candidate =>
                    decide
                      (attachment.diagram.Encloses candidate
                        (attachment.hostRegion site))).bind (fun child =>
                  (compileRegionFrame? definitions attachment.diagram
                    (attachment.hostRegion site)
                    (sourceChildFuel + fragment.val.diagram.regionCount)
                    child
                    ((hostContext attachment sourceOuter).extend
                      (attachment.hostRegion region))).bind (fun nested =>
                    (compileSiblingFrame? definitions attachment.diagram
                      (sourceChildFuel + fragment.val.diagram.regionCount)
                      ((hostContext attachment sourceOuter).extend
                        (attachment.hostRegion region))
                      child nested nodes
                      (attachment.diagram.childrenOf
                        (attachment.hostRegion region))).bind (fun around =>
                        some
                          { visible := around.visible
                            siteBody := around.siteBody
                            context := bindContextFor attachment.diagram
                              (hostContext attachment sourceOuter).ids
                              (attachment.diagram.wiresAt
                                (attachment.hostRegion region))
                              around.context })))) =
                some targetFrame
            rw [targetNodesCompiled']
            rw [hostChildren_offsite compiled region atSite]
            rw [findHostEnclosing compiled, selectedFound]
            change
              (compileRegionFrame? definitions attachment.diagram
                (attachment.hostRegion site)
                (sourceChildFuel + fragment.val.diagram.regionCount)
                (attachment.hostRegion selected)
                ((hostContext attachment sourceOuter).extend
                  (attachment.hostRegion region))).bind (fun nested =>
                (compileSiblingFrame? definitions attachment.diagram
                  (sourceChildFuel + fragment.val.diagram.regionCount)
                  ((hostContext attachment sourceOuter).extend
                    (attachment.hostRegion region))
                  (attachment.hostRegion selected) nested targetNodes'
                  ((base.val.childrenOf region).map
                    attachment.hostRegion)).bind (fun around =>
                    some
                      { visible := around.visible
                        siteBody := around.siteBody
                        context := bindContextFor attachment.diagram
                          (hostContext attachment sourceOuter).ids
                          (attachment.diagram.wiresAt
                            (attachment.hostRegion region))
                          around.context })) =
                some targetFrame
            rw [targetNestedCompiled']
            change
              (compileSiblingFrame? definitions attachment.diagram
                (sourceChildFuel + fragment.val.diagram.regionCount)
                ((hostContext attachment sourceOuter).extend
                  (attachment.hostRegion region))
                (attachment.hostRegion selected) targetNested' targetNodes'
                ((base.val.childrenOf region).map
                  attachment.hostRegion)).bind (fun around =>
                    some
                      { visible := around.visible
                        siteBody := around.siteBody
                        context := bindContextFor attachment.diagram
                          (hostContext attachment sourceOuter).ids
                          (attachment.diagram.wiresAt
                            (attachment.hostRegion region))
                          around.context }) =
                some targetFrame
            rw [targetAroundCompiled']
            rfl
        · change targetAround'.visible =
            generatedSiteContext attachment siteOuter
          exact targetAroundVisible'.trans
            (targetAroundVisible.trans targetNestedVisible)
        · simpa [targetFrame, targetAround'] using
            (GeneratedFrameProvenance.ancestor sourceChildFuel sourceOuter
              siteOuter region selected atSite sourceAbove sourceNodes
              targetNodes sourceNested targetNested sourceAround targetAround
              sourceNodesCompiled targetNodesCompiled selectedFound
              sourceNestedCompiled siblingProvenance childrenNodup
              otherOutside allChildrenAbove nestedProvenance)

end NaturalityInternal

/--
One accepted base factorization and its source-driven generated attachment
counterpart. The generated compiler fuel includes the fragment's certified
region fuel; callers supply no generated compiler equation or context.
-/
structure PairedGeneratedFrame
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (sourceFuel : Nat)
    (sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val)
    (sourceFrame : RegionFrame definitions base.val sourceOuter)
    (targetFrame :
      RegionFrame definitions attachment.diagram
        (NaturalityInternal.hostContext attachment sourceOuter)) : Prop where
  sourceAbove :
    ConcreteElaboration.ContextAbove base.val sourceOuter region
  siteVisible :
    compiled.site.frame.visible = siteOuter.extend site
  sourceVisible :
    sourceFrame.visible = siteOuter.extend site
  sourceGenerated :
    compileRegionFrame? definitions base.val site sourceFuel region
        sourceOuter =
      some sourceFrame
  provenance :
    NaturalityInternal.GeneratedFrameProvenance compiled sourceFuel
      sourceOuter siteOuter region sourceFrame targetFrame

/--
Generate the attachment half solely from the accepted insertion compilation
and the accepted base frame.
-/
theorem pairedGeneratedFrame
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (sourceFuel : Nat)
    (sourceOuter siteOuter :
      ConcreteElaboration.WireContext base.val)
    (sourceFrame :
      RegionFrame definitions base.val sourceOuter)
    (sourceAbove :
      ConcreteElaboration.ContextAbove base.val sourceOuter region)
    (siteVisible :
      compiled.site.frame.visible = siteOuter.extend site)
    (sourceVisible :
      sourceFrame.visible = siteOuter.extend site)
    (sourceGenerated :
      compileRegionFrame? definitions base.val site sourceFuel region
          sourceOuter =
        some sourceFrame) :
    ∃ targetFrame :
        RegionFrame definitions attachment.diagram
          (NaturalityInternal.hostContext attachment sourceOuter),
      PairedGeneratedFrame compiled region sourceFuel sourceOuter siteOuter
        sourceFrame targetFrame := by
  obtain ⟨targetFrame, _, _, provenance⟩ :=
    NaturalityInternal.compileRegionFrame_generate compiled sourceFuel
      sourceOuter region sourceAbove siteOuter siteVisible sourceVisible
      sourceGenerated
  exact ⟨targetFrame,
      { sourceAbove := sourceAbove
        siteVisible := siteVisible
        sourceVisible := sourceVisible
        sourceGenerated := sourceGenerated
        provenance := provenance }⟩

end InsertionCompilation
end VisualProof
