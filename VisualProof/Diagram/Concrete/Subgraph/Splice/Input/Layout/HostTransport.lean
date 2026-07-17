import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.Core

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

private theorem frameWire_visible_at_site
    (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier)
    (hvisible : input.coalesceFrameRaw.Encloses
      (input.coalesceFrameRaw.wires wire).scope input.site) :
    layout.plugRaw.Encloses
      (layout.plugRaw.wires (layout.frameWire wire)).scope
      (layout.frameRegion input.site) := by
  have hframe : input.frame.val.Encloses
      (input.coalescedScope wire) input.site :=
    (input.coalesceFrameRaw_encloses_iff _ _).1 (by
      simpa only [coalesceFrameRaw_wire] using hvisible)
  have hmapped := layout.frame_encloses hframe
  change layout.plugRaw.Encloses
    (layout.plugWire (layout.quotientBlockWire wire)).scope
    (layout.frameRegion input.site)
  rw [plugWire_quotientBlockWire]
  exact hmapped

private theorem frameWire_visible_at_site_iff
    (layout : PlugLayout input)
    (wire : input.wireQuotient.Carrier) :
    layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.frameWire wire)).scope
        (layout.frameRegion input.site) ↔
      input.coalesceFrameRaw.Encloses
        (input.coalesceFrameRaw.wires wire).scope input.site := by
  change layout.plugRaw.Encloses
      (layout.plugWire (layout.quotientBlockWire wire)).scope
      (layout.frameRegion input.site) ↔ _
  rw [plugWire_quotientBlockWire]
  change layout.plugRaw.Encloses
      (layout.frameRegion (input.coalescedScope wire))
      (layout.frameRegion input.site) ↔ _
  rw [layout.frame_encloses_iff,
    input.coalesceFrameRaw_encloses_iff]
  rfl

/-- Canonical lexical index transport for the coalesced host at the splice
site.  It is defined from exact compiler contexts, not from list order. -/
noncomputable def hostSiteWireIndexMap
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Fin (hostLeaf.inheritedWires.extend input.site).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    let wire := (hostLeaf.inheritedWires.extend input.site).get index
    outputLeaf.siteWireIndex outputWitness (layout.frameWire wire)
      (layout.frameWire_visible_at_site wire
        ((hostLeaf.wiresExact.mem_iff wire).1
          (List.get_mem _ index)))

theorem hostSiteWireIndexMap_spec
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (index : Fin (hostLeaf.inheritedWires.extend input.site).length) :
    (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).get
        (layout.hostSiteWireIndexMap hostWitness hostLeaf outputWitness
          outputLeaf index) =
      layout.frameWire
        ((hostLeaf.inheritedWires.extend input.site).get index) := by
  unfold hostSiteWireIndexMap
  exact outputLeaf.siteWireIndex_spec outputWitness _ _

theorem frameWire_mem_outputSiteContext_iff
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (wire : input.wireQuotient.Carrier) :
    layout.frameWire wire ∈
        outputLeaf.inheritedWires.extend (layout.frameRegion input.site) ↔
      wire ∈ hostLeaf.inheritedWires.extend input.site := by
  calc
    layout.frameWire wire ∈ outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site) ↔
        layout.plugRaw.Encloses
          (layout.plugRaw.wires (layout.frameWire wire)).scope
          (layout.frameRegion input.site) :=
      outputLeaf.wiresExact.mem_iff (layout.frameWire wire)
    _ ↔ input.coalesceFrameRaw.Encloses
          (input.coalesceFrameRaw.wires wire).scope input.site :=
      layout.frameWire_visible_at_site_iff wire
    _ ↔ wire ∈ hostLeaf.inheritedWires.extend input.site :=
      (hostLeaf.wiresExact.mem_iff wire).symm

private theorem hostRelationTarget_exists
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {arity : Nat}
    (relation : Theory.RelVar hostWitness.toFocus.holeRels arity) :
    ∃ target : Theory.RelVar outputWitness.toFocus.holeRels arity,
      outputLeaf.binders
          (layout.frameRegion
            (hostLeaf.binderEnumeration.binder relation.index)) =
        some ⟨arity, target⟩ := by
  obtain ⟨parent, hbubble⟩ :=
    hostLeaf.binderEnumeration.bubble relation.index
  have htargetBubble : layout.plugRaw.regions
      (layout.frameRegion
        (hostLeaf.binderEnumeration.binder relation.index)) =
      .bubble (layout.frameRegion parent) arity := by
    change layout.plugRegion
      (layout.frameRegion
        (hostLeaf.binderEnumeration.binder relation.index)) = _
    rw [layout.plugRegion_frameRegion]
    change layout.mapFrameRegion
      (input.coalesceFrameRaw.regions
        (hostLeaf.binderEnumeration.binder relation.index)) = _
    rw [hbubble, relation.hasArity]
    rfl
  have hsourceEncloses :=
    hostLeaf.binderEnumeration.encloses relation.index
  have htargetEncloses : layout.plugRaw.Encloses
      (layout.frameRegion
        (hostLeaf.binderEnumeration.binder relation.index))
      (layout.frameRegion input.site) :=
    layout.frame_encloses
      ((input.coalesceFrameRaw_encloses_iff _ _).1 hsourceEncloses)
  exact outputLeaf.bindersCover _ _ _ htargetBubble htargetEncloses

/-- Relation-variable transport at the host side of the seam, indexed by the
owning concrete bubble rather than by an assumed de Bruijn coincidence. -/
noncomputable def hostRelationRenaming
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    RelationRenaming hostWitness.toFocus.holeRels
      outputWitness.toFocus.holeRels :=
  fun relation => Classical.choose
    (layout.hostRelationTarget_exists hostWitness hostLeaf outputWitness
      outputLeaf relation)

theorem hostRelationRenaming_lookup
    (layout : PlugLayout input)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {arity : Nat}
    (relation : Theory.RelVar hostWitness.toFocus.holeRels arity) :
    outputLeaf.binders
        (layout.frameRegion
          (hostLeaf.binderEnumeration.binder relation.index)) =
      some ⟨arity,
        layout.hostRelationRenaming hostWitness hostLeaf outputWitness
          outputLeaf relation⟩ := by
  exact Classical.choose_spec
    (layout.hostRelationTarget_exists hostWitness hostLeaf outputWitness
      outputLeaf relation)

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

theorem bodyRegion_injective_of_material (layout : PlugLayout input)
    {left right : Fin input.pattern.val.diagram.regionCount}
    (hleft : input.binderSpine.IsMaterialRegion left)
    (hright : input.binderSpine.IsMaterialRegion right)
    (heq : layout.bodyRegion left = layout.bodyRegion right) :
    left = right := by
  rw [layout.bodyRegion_material left hleft,
    layout.bodyRegion_material right hright] at heq
  have hindices := layout.materialRegion_injective heq
  have horigins := congrArg layout.materialRegions.origin hindices
  simpa only [materialIndex, layout.materialRegions.origin_index] using horigins

/-- Material-region parent traversal is reflected as well as preserved by the
plug layout. -/
theorem bodyRegion_climb_between_material_iff
    (layout : PlugLayout input) (steps : Nat)
    (start finish : Fin input.pattern.val.diagram.regionCount)
    (hstart : input.binderSpine.IsMaterialRegion start)
    (hfinish : input.binderSpine.IsMaterialRegion finish) :
    layout.plugRaw.climb steps (layout.bodyRegion start) =
        some (layout.bodyRegion finish) ↔
      input.pattern.val.diagram.climb steps start = some finish := by
  constructor
  · intro htarget
    induction steps generalizing start with
    | zero =>
        have heq : layout.bodyRegion start = layout.bodyRegion finish :=
          Option.some.inj htarget
        exact congrArg some
          (layout.bodyRegion_injective_of_material hstart hfinish heq)
    | succ steps ih =>
        have hparentExists : ∃ parent,
            (input.pattern.val.diagram.regions start).parent? = some parent := by
          cases hregion : input.pattern.val.diagram.regions start with
          | sheet =>
              have hroot :=
                input.pattern.property.diagram_well_formed.only_root_is_sheet
                  start hregion
              exact False.elim (hstart.1 hroot)
          | cut parent => exact ⟨parent, by simp [hregion, CRegion.parent?]⟩
          | bubble parent arity =>
              exact ⟨parent, by simp [hregion, CRegion.parent?]⟩
        obtain ⟨parent, hparent⟩ := hparentExists
        have htail : layout.plugRaw.climb steps
            (layout.bodyRegion parent) = some (layout.bodyRegion finish) := by
          simpa [ConcreteDiagram.climb,
            layout.bodyRegion_parent_exact start parent hstart hparent]
            using htarget
        have hparentMaterial :
            input.binderSpine.IsMaterialRegion parent := by
          by_cases hcandidate :
              input.binderSpine.IsMaterialRegion parent
          · exact hcandidate
          · have hbody := nonmaterial_parent_eq_bodyContainer input
              start parent hstart hparent hcandidate
            have hreverse : layout.plugRaw.Encloses
                (layout.bodyRegion finish) (layout.frameRegion input.site) := by
              obtain ⟨rootSteps, hroot⟩ :=
                layout.plugRaw_all_regions_reach_root
                  (layout.bodyRegion finish)
              have htoRoot := ConcreteElaboration.climb_add htail hroot
              have hbound :=
                ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
                  layout.plugRaw layout.plugRaw_root_is_sheet
                  layout.plugRaw_all_regions_reach_root htoRoot
              rw [hbody, layout.bodyRegion_bodyContainer] at htail
              exact ⟨⟨steps, by omega⟩, htail⟩
            have hforward := layout.site_encloses_bodyRegion finish
            have heq := checked_encloses_antisymm
              layout.plugRaw_root_is_sheet layout.plugRaw_all_regions_reach_root
              hreverse hforward
            rw [layout.bodyRegion_material finish hfinish] at heq
            exact False.elim
              (layout.frameRegion_ne_materialRegion input.site _ heq.symm)
        have hsourceTail := ih parent hparentMaterial htail
        change input.pattern.val.diagram.climb (Nat.succ steps) start =
          some finish
        simpa [ConcreteDiagram.climb, hparent] using hsourceTail
  · intro hsource
    exact layout.bodyRegion_climb_between_material steps start finish
      hstart hfinish hsource

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

theorem material_encloses_iff (layout : PlugLayout input)
    {ancestor descendant : Fin input.pattern.val.diagram.regionCount}
    (hancestor : input.binderSpine.IsMaterialRegion ancestor)
    (hdescendant : input.binderSpine.IsMaterialRegion descendant) :
    layout.plugRaw.Encloses (layout.bodyRegion ancestor)
        (layout.bodyRegion descendant) ↔
      input.pattern.val.diagram.Encloses ancestor descendant := by
  constructor
  · rintro ⟨steps, htarget⟩
    have hsource :=
      (layout.bodyRegion_climb_between_material_iff steps.val descendant
        ancestor hdescendant hancestor).1 htarget
    obtain ⟨rootSteps, hroot⟩ :=
      input.pattern.property.diagram_well_formed.all_regions_reach_root ancestor
    have htoRoot := ConcreteElaboration.climb_add hsource hroot
    have hbound :=
      ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
        input.pattern.val.diagram
        input.pattern.property.diagram_well_formed.root_is_sheet
        input.pattern.property.diagram_well_formed.all_regions_reach_root
        htoRoot
    exact ⟨⟨steps.val, by omega⟩, hsource⟩
  · exact layout.material_encloses hancestor hdescendant

theorem bodyContainer_encloses_material (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion region) :
    input.pattern.val.diagram.Encloses input.binderSpine.bodyContainer
      region := by
  obtain ⟨rootSteps, hroot⟩ :=
    input.pattern.property.diagram_well_formed.all_regions_reach_root region
  obtain ⟨steps, hbody, _⟩ :=
    layout.material_climb_body_and_plug_site rootSteps.val region hmaterial
      hroot
  obtain ⟨bodyRootSteps, hbodyRoot⟩ :=
    input.pattern.property.diagram_well_formed.all_regions_reach_root
      input.binderSpine.bodyContainer
  have htoRoot := ConcreteElaboration.climb_add hbody hbodyRoot
  have hbound :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_le_regionCount
      input.pattern.val.diagram
      input.pattern.property.diagram_well_formed.root_is_sheet
      input.pattern.property.diagram_well_formed.all_regions_reach_root htoRoot
  exact ⟨⟨steps, by omega⟩, hbody⟩

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

theorem exposedWire_get_injective (input : Input signature) :
    Function.Injective input.pattern.val.exposedWires.get := by
  intro first second heq
  apply Fin.ext
  exact (List.getElem_inj input.pattern.val.exposedWires_nodup).mp (by
    simpa only [List.get_eq_getElem] using heq)

/-- The unique exposed-boundary position naming an exposed pattern wire. -/
noncomputable def exposedWireIndex (input : Input signature)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (hexposed : wire ∈ input.pattern.val.exposedWires) :
    Fin input.pattern.val.exposedWires.length :=
  Classical.choose (List.mem_iff_get.mp hexposed)

@[simp] theorem exposedWireIndex_get (input : Input signature)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (hexposed : wire ∈ input.pattern.val.exposedWires) :
    input.pattern.val.exposedWires.get
        (exposedWireIndex input wire hexposed) = wire :=
  Classical.choose_spec (List.mem_iff_get.mp hexposed)

/-- Canonical image of every pattern wire in the plugged diagram.  Exposed
wires use their attached host quotient; every other wire uses its stable
internal block index. -/
noncomputable def patternPlugWire (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    Fin layout.plugRaw.wireCount :=
  if hexposed : wire ∈ input.pattern.val.exposedWires then
    layout.quotientBlockWire
      (layout.exposedAttachment (exposedWireIndex input wire hexposed))
  else
    layout.internalBlockWire
      (layout.internalWires.index wire
        ((layout.internalWires_survives_iff wire).2 hexposed))

theorem patternPlugWire_exposed (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (hexposed : wire ∈ input.pattern.val.exposedWires) :
    layout.patternPlugWire wire =
      layout.quotientBlockWire
        (layout.exposedAttachment (exposedWireIndex input wire hexposed)) := by
  simp only [patternPlugWire, dif_pos hexposed]

theorem patternPlugWire_internal (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (hinternal : wire ∉ input.pattern.val.exposedWires) :
    layout.patternPlugWire wire =
      layout.internalBlockWire
        (layout.internalWires.index wire
          ((layout.internalWires_survives_iff wire).2 hinternal)) := by
  simp only [patternPlugWire, dif_neg hinternal]

/-- A pattern wire is lexically visible at the terminal body exactly when its
canonical plugged image is visible at the host splice site. -/
theorem patternPlugWire_visible_at_site_iff
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
        (layout.frameRegion input.site) ↔
      input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires wire).scope
        input.binderSpine.bodyContainer := by
  by_cases hexposed : wire ∈ input.pattern.val.exposedWires
  · have hsourceScope :
        (input.pattern.val.diagram.wires wire).scope =
          input.pattern.val.diagram.root :=
      input.pattern.property.boundary_is_root_scoped wire
        ((OpenConcreteDiagram.mem_exposedWires _ wire).1 hexposed)
    have hsourceVisible : input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires wire).scope
        input.binderSpine.bodyContainer := by
      rw [hsourceScope]
      exact input.pattern.property.diagram_well_formed.all_regions_reach_root _
    have htargetVisible : layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
        (layout.frameRegion input.site) := by
      rw [layout.patternPlugWire_exposed wire hexposed]
      change layout.plugRaw.Encloses
        (layout.plugWire (layout.quotientBlockWire
          (layout.exposedAttachment
            (exposedWireIndex input wire hexposed)))).scope
        (layout.frameRegion input.site)
      rw [plugWire_quotientBlockWire]
      apply layout.frame_encloses
      apply (input.coalesceFrameRaw_encloses_iff _ _).1
      simpa only [coalesceFrameRaw_wire, exposedAttachment] using
        input.quotientAttachment_visible hadmissible
          (layout.exposedPosition (exposedWireIndex input wire hexposed))
    exact ⟨fun _ => hsourceVisible, fun _ => htargetVisible⟩
  · rw [layout.patternPlugWire_internal wire hexposed]
    change layout.plugRaw.Encloses
        (layout.plugWire (layout.internalBlockWire
          (layout.internalWires.index wire
            ((layout.internalWires_survives_iff wire).2 hexposed)))).scope
        (layout.frameRegion input.site) ↔ _
    rw [plugWire_internalBlockWire]
    simp only [mapPatternWire]
    rw [layout.internalWires.origin_index wire
      ((layout.internalWires_survives_iff wire).2 hexposed)]
    rcases patternInternalWire_scope_material_or_bodyContainer input wire
        hexposed with hmaterial | hbody
    · constructor
      · intro htarget
        have hsite := layout.site_encloses_bodyRegion
          (input.pattern.val.diagram.wires wire).scope
        have heq := checked_encloses_antisymm
          layout.plugRaw_root_is_sheet layout.plugRaw_all_regions_reach_root
          htarget hsite
        rw [layout.bodyRegion_material _ hmaterial] at heq
        exact False.elim
          (layout.frameRegion_ne_materialRegion input.site _ heq.symm)
      · intro hsource
        exact False.elim
          (layout.material_not_encloses_bodyContainer _ hmaterial hsource)
    · rw [hbody, layout.bodyRegion_bodyContainer]
      constructor <;> intro _ <;> exact ConcreteDiagram.Encloses.refl _ _

/-- Visibility reflection extends recursively through every retained material
region. -/
theorem patternPlugWire_visible_at_material_iff
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
        (layout.bodyRegion region) ↔
      input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires wire).scope region := by
  by_cases hexposed : wire ∈ input.pattern.val.exposedWires
  · have hsourceScope :
        (input.pattern.val.diagram.wires wire).scope =
          input.pattern.val.diagram.root :=
      input.pattern.property.boundary_is_root_scoped wire
        ((OpenConcreteDiagram.mem_exposedWires _ wire).1 hexposed)
    have hsourceVisible : input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires wire).scope region := by
      rw [hsourceScope]
      exact input.pattern.property.diagram_well_formed.all_regions_reach_root _
    have htargetVisible : layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
        (layout.bodyRegion region) := by
      rw [layout.patternPlugWire_exposed wire hexposed]
      change layout.plugRaw.Encloses
        (layout.plugWire (layout.quotientBlockWire
          (layout.exposedAttachment
            (exposedWireIndex input wire hexposed)))).scope
        (layout.bodyRegion region)
      rw [plugWire_quotientBlockWire]
      have hsite : layout.plugRaw.Encloses
          (layout.frameRegion
            (input.coalescedScope (layout.exposedAttachment
              (exposedWireIndex input wire hexposed))))
          (layout.frameRegion input.site) := by
        apply layout.frame_encloses
        apply (input.coalesceFrameRaw_encloses_iff _ _).1
        simpa only [coalesceFrameRaw_wire, exposedAttachment] using
          input.quotientAttachment_visible hadmissible
            (layout.exposedPosition (exposedWireIndex input wire hexposed))
      exact layout.plugRaw_encloses_trans hsite
        (layout.site_encloses_bodyRegion region)
    exact ⟨fun _ => hsourceVisible, fun _ => htargetVisible⟩
  · rw [layout.patternPlugWire_internal wire hexposed]
    change layout.plugRaw.Encloses
        (layout.plugWire (layout.internalBlockWire
          (layout.internalWires.index wire
            ((layout.internalWires_survives_iff wire).2 hexposed)))).scope
        (layout.bodyRegion region) ↔ _
    rw [plugWire_internalBlockWire]
    simp only [mapPatternWire]
    rw [layout.internalWires.origin_index wire
      ((layout.internalWires_survives_iff wire).2 hexposed)]
    rcases patternInternalWire_scope_material_or_bodyContainer input wire
        hexposed with hscope | hscope
    · exact layout.material_encloses_iff hscope hregion
    · rw [hscope, layout.bodyRegion_bodyContainer]
      exact ⟨fun _ => layout.bodyContainer_encloses_material region hregion,
        fun _ => layout.site_encloses_bodyRegion region⟩

/-- Internal-wire carriers owned exactly by one retained material region. -/
def materialInternalCarriers (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    List layout.internalWires.Carrier :=
  filterFin fun internal => decide
    ((input.pattern.val.diagram.wires
      (layout.internalWires.origin internal)).scope = region)

def materialOriginalWires (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    List (Fin input.pattern.val.diagram.wireCount) :=
  (layout.materialInternalCarriers region).map layout.internalWires.origin

theorem mem_materialOriginalWires_iff
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    wire ∈ layout.materialOriginalWires region ↔
      (input.pattern.val.diagram.wires wire).scope = region := by
  constructor
  · intro hmember
    obtain ⟨internal, hinternal, horigin⟩ := List.mem_map.mp hmember
    have hscope := decide_eq_true_iff.mp
      ((mem_filterFin internal).1 hinternal)
    simpa only [horigin] using hscope
  · intro hscope
    have hnotExposed : wire ∉ input.pattern.val.exposedWires := by
      intro hexposed
      have hroot := input.pattern.property.boundary_is_root_scoped wire
        ((OpenConcreteDiagram.mem_exposedWires _ wire).1 hexposed)
      exact hregion.1 (hscope.symm.trans hroot)
    let internal := layout.internalWires.index wire
      ((layout.internalWires_survives_iff wire).2 hnotExposed)
    apply List.mem_map.mpr
    refine ⟨internal, ?_, layout.internalWires.origin_index _ _⟩
    apply (mem_filterFin internal).2
    apply decide_eq_true_iff.mpr
    simpa only [internal, layout.internalWires.origin_index] using hscope

theorem materialOriginalWires_nodup
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    (layout.materialOriginalWires region).Nodup := by
  exact (filterFin_nodup _).map layout.internalWires.origin
    (fun left right hne heq => hne
      (layout.internalWires.origin_injective heq))

def materialSemanticWires (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    List (Fin layout.plugRaw.wireCount) :=
  (layout.materialInternalCarriers region).map layout.internalWire

theorem materialSemanticWires_subset
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    ∀ wire, wire ∈ layout.materialSemanticWires region →
      wire ∈ ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.bodyRegion region) := by
  intro wire hmember
  obtain ⟨internal, hinternal, rfl⟩ := List.mem_map.mp hmember
  have hscope := decide_eq_true_iff.mp
    ((mem_filterFin internal).1 hinternal)
  rw [ConcreteElaboration.mem_exactScopeWires]
  change (layout.plugWire (layout.internalBlockWire internal)).scope = _
  rw [plugWire_internalBlockWire]
  simpa only [mapPatternWire] using congrArg layout.bodyRegion hscope

theorem materialSemanticWires_complete
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    ∀ wire, wire ∈ ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.bodyRegion region) →
      wire ∈ layout.materialSemanticWires region := by
  intro wire hmember
  revert hmember
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun quotient => ?_)
    (fun internal => ?_) wire
  · intro hmember
    rw [ConcreteElaboration.mem_exactScopeWires] at hmember
    change (layout.plugWire (layout.quotientBlockWire quotient)).scope = _
      at hmember
    rw [plugWire_quotientBlockWire,
      layout.bodyRegion_material region hregion] at hmember
    exact False.elim
      (layout.frameRegion_ne_materialRegion _ _ hmember)
  · intro hmember
    rw [ConcreteElaboration.mem_exactScopeWires] at hmember
    change (layout.plugWire (layout.internalBlockWire internal)).scope = _
      at hmember
    rw [plugWire_internalBlockWire] at hmember
    simp only [mapPatternWire] at hmember
    let original := layout.internalWires.origin internal
    have hinternal : original ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff original).1
        (layout.internalWires.origin_survives internal)
    have hscope : (input.pattern.val.diagram.wires original).scope = region := by
      rcases patternInternalWire_scope_material_or_bodyContainer input original
          hinternal with hmaterial | hbody
      · exact layout.bodyRegion_injective_of_material hmaterial hregion
          hmember
      · rw [hbody, layout.bodyRegion_bodyContainer,
          layout.bodyRegion_material region hregion] at hmember
        exact False.elim
          (layout.frameRegion_ne_materialRegion input.site _ hmember)
    apply List.mem_map.mpr
    refine ⟨internal, ?_, rfl⟩
    exact (mem_filterFin internal).2 (decide_eq_true_iff.mpr hscope)

theorem materialSemanticWires_nodup
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    (layout.materialSemanticWires region).Nodup := by
  exact (filterFin_nodup _).map layout.internalWire
    (fun left right hne heq => hne (layout.internalWire_injective heq))

def materialSourceWireEquiv
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    FiniteEquiv (Fin (layout.materialInternalCarriers region).length)
      (Fin (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        region).length) :=
  (FiniteEquiv.finCast (List.length_map _).symm).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount))
      (layout.materialOriginalWires region)
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram region)
      (layout.materialOriginalWires_nodup region)
      (ConcreteElaboration.exactScopeWires_nodup _ _)
      (fun wire => by
        simpa using
          (layout.mem_materialOriginalWires_iff region hregion wire).symm))

def materialTargetWireEquiv
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    FiniteEquiv (Fin (layout.materialInternalCarriers region).length)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.bodyRegion region)).length) :=
  (FiniteEquiv.finCast (List.length_map _).symm).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
      (layout.materialSemanticWires region)
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.bodyRegion region))
      (layout.materialSemanticWires_nodup region)
      (ConcreteElaboration.exactScopeWires_nodup _ _)
      (fun wire => ⟨layout.materialSemanticWires_complete region hregion wire,
        layout.materialSemanticWires_subset region wire⟩))

def materialLocalWireEquiv
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    FiniteEquiv
      (Fin (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        region).length)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.bodyRegion region)).length) :=
  (layout.materialSourceWireEquiv region hregion).symm.trans
    (layout.materialTargetWireEquiv region hregion)

theorem materialLocalWireEquiv_spec
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram region).length) :
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.bodyRegion region)).get
        (layout.materialLocalWireEquiv region hregion index) =
      layout.patternPlugWire
        ((ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          region).get index) := by
  let carrier := (layout.materialSourceWireEquiv region hregion).symm index
  have hsource := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.wireCount))
    (layout.materialOriginalWires region)
    (ConcreteElaboration.exactScopeWires input.pattern.val.diagram region)
    (layout.materialOriginalWires_nodup region)
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (fun wire => by
      simpa using
        (layout.mem_materialOriginalWires_iff region hregion wire).symm)
    (Fin.cast (List.length_map _).symm carrier)
  have htarget := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    (layout.materialSemanticWires region)
    (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.bodyRegion region))
    (layout.materialSemanticWires_nodup region)
    (ConcreteElaboration.exactScopeWires_nodup _ _)
    (fun wire => ⟨layout.materialSemanticWires_complete region hregion wire,
      layout.materialSemanticWires_subset region wire⟩)
    (Fin.cast (List.length_map _).symm carrier)
  have hsourceCarrier :
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        region).get index = layout.internalWires.origin
          ((layout.materialInternalCarriers region).get carrier) := by
    have hsource' :
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          region).get
            (layout.materialSourceWireEquiv region hregion carrier) =
          layout.internalWires.origin
            ((layout.materialInternalCarriers region).get carrier) := by
      simpa [materialSourceWireEquiv, materialOriginalWires,
        FiniteEquiv.finCast] using hsource
    have hcarrier : layout.materialSourceWireEquiv region hregion carrier =
        index := by
      exact FiniteEquiv.apply_symm_apply
        (layout.materialSourceWireEquiv region hregion) index
    rw [hcarrier] at hsource'
    exact hsource'
  have htargetCarrier :
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        (layout.bodyRegion region)).get
          (layout.materialTargetWireEquiv region hregion carrier) =
        layout.internalWire
          ((layout.materialInternalCarriers region).get carrier) := by
    simpa [materialTargetWireEquiv, materialSemanticWires,
      FiniteEquiv.finCast] using htarget
  rw [materialLocalWireEquiv, FiniteEquiv.trans_apply]
  change _ = layout.patternPlugWire _
  rw [hsourceCarrier]
  have hinternal : layout.internalWires.origin
      ((layout.materialInternalCarriers region).get carrier) ∉
        input.pattern.val.exposedWires :=
    (layout.internalWires_survives_iff _).1
      (layout.internalWires.origin_survives _)
  rw [layout.patternPlugWire_internal _ hinternal,
    layout.internalWires.index_origin]
  exact htargetCarrier

/-- The recursive wire map: caller-supplied inherited transport followed by
the exact permutation of wires bound by this material region. -/
def materialExtendedWireMap
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.extend (layout.bodyRegion region)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend targetContext
        (layout.bodyRegion region)).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.bodyRegion region)).length (outerMap outer))
        (fun localIndex => Fin.natAdd targetContext.length
          (layout.materialLocalWireEquiv region hregion localIndex))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext region)
          index))

/-- The source side of the recursive factorization: inherited wires are
substituted, while locally bound wires keep their source positions. -/
def materialSourceExtendedWireMap
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          region).length) :=
  fun index =>
    Fin.addCases
      (fun outer => Fin.castAdd
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          region).length (outerMap outer))
      (fun localIndex => Fin.natAdd targetContext.length localIndex)
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend sourceContext region)
        index)

theorem materialSourceExtendedWireMap_eq
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    layout.materialSourceExtendedWireMap region sourceContext targetContext
        outerMap =
      extendWireRenaming outerMap
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            region).length ∘
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext region) := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split <;>
    simp [materialSourceExtendedWireMap, split, extendWireRenaming]

theorem finishRegion_renameWires_renameRelations
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (items : ItemSeq signature (sourceContext.extend region).length sourceRels) :
    ((ConcreteElaboration.finishRegion input.pattern.val.diagram sourceContext
        region items).renameWires outerMap).renameRelations relationMap =
      .mk (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          region).length
        ((items.renameWires
          (layout.materialSourceExtendedWireMap region sourceContext
            targetContext outerMap)).renameRelations relationMap) := by
  simp only [ConcreteElaboration.finishRegion, Region.renameWires,
    Region.renameRelations, ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp]
  rw [layout.materialSourceExtendedWireMap_eq region sourceContext
    targetContext outerMap]

theorem materialExtendedWireMap_factor
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length) :
    (fun index =>
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend targetContext
          (layout.bodyRegion region)).symm
        (extendWireEquiv (FiniteEquiv.refl (Fin targetContext.length))
          (layout.materialLocalWireEquiv region hregion)
          (layout.materialSourceExtendedWireMap region sourceContext
            targetContext outerMap index))) =
      layout.materialExtendedWireMap region hregion sourceContext
        targetContext outerMap := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split <;>
    simp [materialExtendedWireMap, materialSourceExtendedWireMap, split,
      extendWireEquiv, FiniteEquiv.refl]

theorem materialExtendedWireMap_spec
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceContext.length → Fin targetContext.length)
    (outerSpec : ∀ index, targetContext.get (outerMap index) =
      layout.patternPlugWire (sourceContext.get index))
    (index : Fin (sourceContext.extend region).length) :
    (targetContext.extend (layout.bodyRegion region)).get
        (layout.materialExtendedWireMap region hregion sourceContext
          targetContext outerMap index) =
      layout.patternPlugWire ((sourceContext.extend region).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simpa [materialExtendedWireMap, split,
      ConcreteElaboration.WireContext.extend] using outerSpec outer
  · simpa [materialExtendedWireMap, split,
      ConcreteElaboration.WireContext.extend] using
        layout.materialLocalWireEquiv_spec region hregion localIndex

def materialSemanticOccurrences (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    List (ConcreteElaboration.LocalOccurrence layout.plugRaw.regionCount
      layout.plugRaw.nodeCount) :=
  (ConcreteElaboration.localOccurrences input.pattern.val.diagram region).map
    layout.mapPatternOccurrence

theorem mapPatternOccurrence_mem_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount input.pattern.val.diagram.nodeCount)
    (hmem : occurrence ∈ ConcreteElaboration.localOccurrences
      input.pattern.val.diagram region) :
    layout.mapPatternOccurrence occurrence ∈
      ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.bodyRegion region) := by
  cases occurrence with
  | node node =>
      have hnode :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hmem
      simp only [mapPatternOccurrence]
      rw [ConcreteElaboration.mem_localOccurrences_node]
      change (layout.plugNode (layout.patternNode node)).region = _
      rw [layout.plugNode_patternNode, layout.mapPatternNode_region, hnode]
  | child child =>
      have hparent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hmem
      have hchild := directChildOfMaterial_material input region child
        hregion hparent
      simp only [mapPatternOccurrence]
      rw [ConcreteElaboration.mem_localOccurrences_child]
      exact layout.bodyRegion_parent_exact child region hchild hparent

theorem mapPatternOccurrence_injective_on_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    ∀ left, left ∈ ConcreteElaboration.localOccurrences
        input.pattern.val.diagram region →
      ∀ right, right ∈ ConcreteElaboration.localOccurrences
        input.pattern.val.diagram region →
        layout.mapPatternOccurrence left = layout.mapPatternOccurrence right →
          left = right := by
  intro left hleft right hright heq
  cases left with
  | node leftNode =>
      cases right with
      | node rightNode =>
          exact congrArg ConcreteElaboration.LocalOccurrence.node
            (layout.patternNode_injective
              (ConcreteElaboration.LocalOccurrence.node.inj heq))
      | child rightChild => contradiction
  | child leftChild =>
      cases right with
      | node rightNode => contradiction
      | child rightChild =>
          have hleftParent :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hleft
          have hrightParent :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hright
          have hleftMaterial := directChildOfMaterial_material input region
            leftChild hregion hleftParent
          have hrightMaterial := directChildOfMaterial_material input region
            rightChild hregion hrightParent
          have hregions := ConcreteElaboration.LocalOccurrence.child.inj heq
          exact congrArg ConcreteElaboration.LocalOccurrence.child
            (layout.bodyRegion_injective_of_material hleftMaterial
              hrightMaterial hregions)

theorem materialSemanticOccurrences_complete
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    ∀ occurrence, occurrence ∈ ConcreteElaboration.localOccurrences
        layout.plugRaw (layout.bodyRegion region) →
      ∃ original, original ∈ ConcreteElaboration.localOccurrences
          input.pattern.val.diagram region ∧
        layout.mapPatternOccurrence original = occurrence := by
  intro occurrence hmem
  cases occurrence with
  | node node =>
      revert hmem
      refine Fin.addCases (m := input.frame.val.nodeCount)
        (n := input.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
        (fun patternNode => ?_) node
      · intro hmem
        have htarget :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hmem
        change (layout.plugNode (layout.frameNode frameNode)).region =
          layout.bodyRegion region at htarget
        rw [layout.plugNode_frameNode, layout.mapFrameNode_region,
          layout.bodyRegion_material region hregion] at htarget
        exact False.elim
          (layout.frameRegion_ne_materialRegion _ _ htarget)
      · intro hmem
        have htarget :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hmem
        change (layout.plugNode (layout.patternNode patternNode)).region =
          layout.bodyRegion region at htarget
        rw [layout.plugNode_patternNode, layout.mapPatternNode_region]
          at htarget
        rcases patternNode_region_material_or_bodyContainer input patternNode with
          hnodeMaterial | hnodeBody
        · have hnodeRegion := layout.bodyRegion_injective_of_material
            hnodeMaterial hregion htarget
          exact ⟨.node patternNode,
            (ConcreteElaboration.mem_localOccurrences_node _ _ _).2
              hnodeRegion,
            rfl⟩
        · rw [hnodeBody, layout.bodyRegion_bodyContainer,
            layout.bodyRegion_material region hregion] at htarget
          exact False.elim
            (layout.frameRegion_ne_materialRegion _ _ htarget)
  | child child =>
      revert hmem
      refine Fin.addCases (m := input.frame.val.regionCount)
        (n := layout.materialRegions.count) (fun frameChild => ?_)
        (fun materialChild => ?_) child
      · intro hmem
        have htarget :=
          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hmem
        change (layout.plugRegion (layout.frameRegion frameChild)).parent? =
          some (layout.bodyRegion region) at htarget
        rw [layout.plugRegion_frameRegion] at htarget
        cases hsource : input.frame.val.regions frameChild with
        | sheet => simp [hsource, mapFrameRegion, CRegion.parent?] at htarget
        | cut parent =>
            have heq : layout.frameRegion parent = layout.bodyRegion region :=
              Option.some.inj (by
                simpa [hsource, mapFrameRegion, CRegion.parent?] using htarget)
            rw [layout.bodyRegion_material region hregion] at heq
            exact False.elim
              (layout.frameRegion_ne_materialRegion _ _ heq)
        | bubble parent arity =>
            have heq : layout.frameRegion parent = layout.bodyRegion region :=
              Option.some.inj (by
                simpa [hsource, mapFrameRegion, CRegion.parent?] using htarget)
            rw [layout.bodyRegion_material region hregion] at heq
            exact False.elim
              (layout.frameRegion_ne_materialRegion _ _ heq)
      · intro hmem
        let original := layout.materialRegions.origin materialChild
        have horiginalMaterial :
            input.binderSpine.IsMaterialRegion original :=
          (layout.materialRegions_survives_iff original).1
            (layout.materialRegions.origin_survives materialChild)
        have htarget :=
          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hmem
        change (layout.plugRegion (layout.materialRegion materialChild)).parent? =
          some (layout.bodyRegion region) at htarget
        rw [layout.plugRegion_materialRegion] at htarget
        change (layout.mapPatternRegion
          (input.pattern.val.diagram.regions original)).parent? =
            some (layout.bodyRegion region) at htarget
        cases hsource : input.pattern.val.diagram.regions original with
        | sheet =>
            exact False.elim (horiginalMaterial.1
              (input.pattern.property.diagram_well_formed.only_root_is_sheet
                original hsource))
        | cut parent =>
            have hparent :
                (input.pattern.val.diagram.regions original).parent? =
                  some parent := by simp [hsource, CRegion.parent?]
            have hbodyEq : layout.bodyRegion parent =
                layout.bodyRegion region := Option.some.inj (by
              simpa [hsource, mapPatternRegion, CRegion.parent?] using htarget)
            have hparentMaterial :
                input.binderSpine.IsMaterialRegion parent := by
              by_cases hcandidate :
                  input.binderSpine.IsMaterialRegion parent
              · exact hcandidate
              · have hbody := nonmaterial_parent_eq_bodyContainer input
                  original parent horiginalMaterial hparent hcandidate
                rw [hbody, layout.bodyRegion_bodyContainer,
                  layout.bodyRegion_material region hregion] at hbodyEq
                exact False.elim
                  (layout.frameRegion_ne_materialRegion _ _ hbodyEq)
            have hparentEq := layout.bodyRegion_injective_of_material
              hparentMaterial hregion hbodyEq
            refine ⟨.child original,
              (ConcreteElaboration.mem_localOccurrences_child _ _ _).2 ?_, ?_⟩
            · simpa only [hparentEq] using hparent
            · exact congrArg ConcreteElaboration.LocalOccurrence.child
                (layout.bodyRegion_origin materialChild)
        | bubble parent arity =>
            have hparent :
                (input.pattern.val.diagram.regions original).parent? =
                  some parent := by simp [hsource, CRegion.parent?]
            have hbodyEq : layout.bodyRegion parent =
                layout.bodyRegion region := Option.some.inj (by
              simpa [hsource, mapPatternRegion, CRegion.parent?] using htarget)
            have hparentMaterial :
                input.binderSpine.IsMaterialRegion parent := by
              by_cases hcandidate :
                  input.binderSpine.IsMaterialRegion parent
              · exact hcandidate
              · have hbody := nonmaterial_parent_eq_bodyContainer input
                  original parent horiginalMaterial hparent hcandidate
                rw [hbody, layout.bodyRegion_bodyContainer,
                  layout.bodyRegion_material region hregion] at hbodyEq
                exact False.elim
                  (layout.frameRegion_ne_materialRegion _ _ hbodyEq)
            have hparentEq := layout.bodyRegion_injective_of_material
              hparentMaterial hregion hbodyEq
            refine ⟨.child original,
              (ConcreteElaboration.mem_localOccurrences_child _ _ _).2 ?_, ?_⟩
            · simpa only [hparentEq] using hparent
            · exact congrArg ConcreteElaboration.LocalOccurrence.child
                (layout.bodyRegion_origin materialChild)

theorem materialSemanticOccurrences_nodup
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    (layout.materialSemanticOccurrences region).Nodup := by
  let occurrences := ConcreteElaboration.localOccurrences
    input.pattern.val.diagram region
  have mappedNodup : ∀ items : List
      (ConcreteElaboration.LocalOccurrence
        input.pattern.val.diagram.regionCount input.pattern.val.diagram.nodeCount),
      items.Nodup →
      (∀ occurrence, occurrence ∈ items → occurrence ∈ occurrences) →
      (items.map layout.mapPatternOccurrence).Nodup := by
    intro items hnodup hsubset
    induction items with
    | nil => simp
    | cons head tail ih =>
        rw [List.nodup_cons] at hnodup
        rw [List.map, List.nodup_cons]
        constructor
        · intro hmapped
          rw [List.mem_map] at hmapped
          rcases hmapped with ⟨other, hother, heq⟩
          have horiginal := layout.mapPatternOccurrence_injective_on_material
            region hregion head (hsubset head (by simp)) other
              (hsubset other (by simp [hother])) heq.symm
          exact hnodup.1 (horiginal ▸ hother)
        · exact ih hnodup.2 (by
            intro occurrence hoccurrence
            exact hsubset occurrence (by simp [hoccurrence]))
  exact mappedNodup occurrences
    (ConcreteElaboration.localOccurrences_nodup _ _) (fun _ hmem => hmem)

noncomputable def materialOccurrenceEquiv
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    FiniteEquiv
      (Fin (ConcreteElaboration.localOccurrences input.pattern.val.diagram
        region).length)
      (Fin (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.bodyRegion region)).length) :=
  listEmbeddingEquiv layout.mapPatternOccurrence
    (ConcreteElaboration.localOccurrences input.pattern.val.diagram region)
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.bodyRegion region))
    (ConcreteElaboration.localOccurrences_nodup _ _)
    (ConcreteElaboration.localOccurrences_nodup _ _)
    (layout.mapPatternOccurrence_mem_material region hregion)
    (layout.materialSemanticOccurrences_complete region hregion)
    (layout.mapPatternOccurrence_injective_on_material region hregion)

theorem materialOccurrenceEquiv_spec
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (index : Fin (ConcreteElaboration.localOccurrences
      input.pattern.val.diagram region).length) :
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.bodyRegion region)).get
        (layout.materialOccurrenceEquiv region hregion index) =
      layout.mapPatternOccurrence
        ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
          region).get index) := by
  exact listEmbeddingEquiv_spec layout.mapPatternOccurrence
    (ConcreteElaboration.localOccurrences input.pattern.val.diagram region)
    (ConcreteElaboration.localOccurrences layout.plugRaw
      (layout.bodyRegion region)) _ _ _ _ _ index

theorem quotient_endpoint_provenance (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier)
    (endpoint : CEndpoint layout.nodeCount)
    (hoccurs : layout.plugRaw.EndpointOccurs
      (layout.quotientBlockWire quotient) endpoint) :
    (∃ original : CEndpoint input.frame.val.nodeCount,
        original ∈ input.coalescedEndpoints quotient ∧
          layout.mapFrameEndpoint original = endpoint) ∨
      ∃ external : Fin input.pattern.val.exposedWires.length,
        layout.exposedAttachment external = quotient ∧
          ∃ original : CEndpoint input.pattern.val.diagram.nodeCount,
            original ∈ (input.pattern.val.diagram.wires
                (input.pattern.val.exposedWires.get external)).endpoints ∧
              layout.mapPatternEndpoint original = endpoint := by
  unfold ConcreteDiagram.EndpointOccurs at hoccurs
  simp only [plugRaw] at hoccurs
  rw [plugWire_quotientBlockWire signature input layout] at hoccurs
  rcases List.mem_append.mp hoccurs with hframe | hpattern
  · left
    exact List.mem_map.mp hframe
  · right
    exact (layout.mem_boundaryEndpoints quotient endpoint).1 hpattern

theorem internal_endpoint_provenance (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (internal : layout.internalWires.Carrier)
    (endpoint : CEndpoint layout.nodeCount)
    (hoccurs : layout.plugRaw.EndpointOccurs
      (layout.internalBlockWire internal) endpoint) :
    ∃ original : CEndpoint input.pattern.val.diagram.nodeCount,
      original ∈ (input.pattern.val.diagram.wires
          (layout.internalWires.origin internal)).endpoints ∧
        layout.mapPatternEndpoint original = endpoint := by
  unfold ConcreteDiagram.EndpointOccurs at hoccurs
  simp only [plugRaw] at hoccurs
  rw [plugWire_internalBlockWire signature input layout] at hoccurs
  change endpoint ∈
    (input.pattern.val.diagram.wires
      (layout.internalWires.origin internal)).endpoints.map
        layout.mapPatternEndpoint at hoccurs
  exact List.mem_map.mp hoccurs

theorem plugRaw_patternEndpoint_forward
    (layout : PlugLayout input)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount)
    (hoccurs : input.pattern.val.diagram.EndpointOccurs wire endpoint) :
    layout.plugRaw.EndpointOccurs (layout.patternPlugWire wire)
      (layout.mapPatternEndpoint endpoint) := by
  change endpoint ∈ (input.pattern.val.diagram.wires wire).endpoints at hoccurs
  by_cases hexposed : wire ∈ input.pattern.val.exposedWires
  · rw [layout.patternPlugWire_exposed wire hexposed]
    unfold ConcreteDiagram.EndpointOccurs
    simp only [plugRaw]
    rw [plugWire_quotientBlockWire]
    apply List.mem_append_right
    rw [layout.mem_boundaryEndpoints]
    refine ⟨exposedWireIndex input wire hexposed, rfl, endpoint, ?_, rfl⟩
    rw [exposedWireIndex_get]
    exact hoccurs
  · rw [layout.patternPlugWire_internal wire hexposed]
    unfold ConcreteDiagram.EndpointOccurs
    simp only [plugRaw]
    rw [plugWire_internalBlockWire]
    have horigin := layout.internalWires.origin_index wire
      ((layout.internalWires_survives_iff wire).2 hexposed)
    rw [horigin]
    exact List.mem_map.mpr ⟨endpoint, hoccurs, rfl⟩

theorem plugRaw_patternEndpoint_backward
    (layout : PlugLayout input)
    (targetWire : Fin layout.plugRaw.wireCount)
    (endpoint : CEndpoint input.pattern.val.diagram.nodeCount)
    (hoccurs : layout.plugRaw.EndpointOccurs targetWire
      (layout.mapPatternEndpoint endpoint)) :
    ∃ sourceWire : Fin input.pattern.val.diagram.wireCount,
      layout.patternPlugWire sourceWire = targetWire ∧
        input.pattern.val.diagram.EndpointOccurs sourceWire endpoint := by
  revert hoccurs
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun quotient => ?_)
    (fun internal => ?_) targetWire
  · intro hquotient
    rcases quotient_endpoint_provenance _ input layout quotient
        (layout.mapPatternEndpoint endpoint) hquotient with
      ⟨frameEndpoint, _, heq⟩ |
        ⟨external, hattachment, patternEndpoint,
          hsourceOccurs, heq⟩
    · exact False.elim
        (layout.mapFrameEndpoint_ne_mapPatternEndpoint frameEndpoint endpoint
          heq)
    · have hendpoint : patternEndpoint = endpoint :=
        layout.mapPatternEndpoint_injective heq
      subst patternEndpoint
      let sourceWire := input.pattern.val.exposedWires.get external
      have hexposed : sourceWire ∈ input.pattern.val.exposedWires :=
        List.get_mem _ _
      refine ⟨sourceWire, ?_, hsourceOccurs⟩
      rw [layout.patternPlugWire_exposed sourceWire hexposed]
      apply congrArg layout.quotientBlockWire
      rw [← hattachment]
      apply congrArg layout.exposedAttachment
      apply exposedWire_get_injective input
      simp only [exposedWireIndex_get]
      rfl
  · intro hinternal
    obtain ⟨patternEndpoint, hsourceOccurs, heq⟩ :=
      internal_endpoint_provenance _ input layout internal
        (layout.mapPatternEndpoint endpoint) hinternal
    have hendpoint : patternEndpoint = endpoint :=
      layout.mapPatternEndpoint_injective heq
    subst patternEndpoint
    let sourceWire := layout.internalWires.origin internal
    have hsourceInternal : sourceWire ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff sourceWire).1
        (layout.internalWires.origin_survives internal)
    refine ⟨sourceWire, ?_, hsourceOccurs⟩
    rw [layout.patternPlugWire_internal sourceWire hsourceInternal]
    apply congrArg layout.internalBlockWire
    exact layout.internalWires.index_origin internal

end PlugLayout

end VisualProof.Diagram.Splice.Input
