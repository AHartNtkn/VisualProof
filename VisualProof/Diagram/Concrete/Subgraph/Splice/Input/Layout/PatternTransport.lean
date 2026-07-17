import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.HostTransport

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

/-- Canonical lexical index transport for the pattern terminal body. -/
noncomputable def patternSiteWireIndexMap
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Fin (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    let wire := (patternLeaf.inheritedWires.extend
      input.binderSpine.bodyContainer).get index
    outputLeaf.siteWireIndex outputWitness (layout.patternPlugWire wire)
      ((layout.patternPlugWire_visible_at_site_iff hadmissible wire).2
        ((patternLeaf.wiresExact.mem_iff wire).1
          (List.get_mem _ index)))

theorem patternSiteWireIndexMap_spec
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (index : Fin (patternLeaf.inheritedWires.extend
      input.binderSpine.bodyContainer).length) :
    (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).get
        (layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
          outputWitness outputLeaf index) =
      layout.patternPlugWire
        ((patternLeaf.inheritedWires.extend
          input.binderSpine.bodyContainer).get index) := by
  unfold patternSiteWireIndexMap
  exact outputLeaf.siteWireIndex_spec outputWitness _ _

theorem patternPlugWire_mem_outputSiteContext_iff
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.patternPlugWire wire ∈
        outputLeaf.inheritedWires.extend (layout.frameRegion input.site) ↔
      wire ∈ patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer := by
  calc
    layout.patternPlugWire wire ∈ outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site) ↔
        layout.plugRaw.Encloses
          (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
          (layout.frameRegion input.site) :=
      outputLeaf.wiresExact.mem_iff (layout.patternPlugWire wire)
    _ ↔ input.pattern.val.diagram.Encloses
          (input.pattern.val.diagram.wires wire).scope
          input.binderSpine.bodyContainer :=
      layout.patternPlugWire_visible_at_site_iff hadmissible wire
    _ ↔ wire ∈ patternLeaf.inheritedWires.extend
          input.binderSpine.bodyContainer :=
      (patternLeaf.wiresExact.mem_iff wire).symm

private theorem patternRelationTarget_exists
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {arity : Nat}
    (relation : Theory.RelVar patternWitness.toFocus.holeRels arity) :
    ∃ target : Theory.RelVar outputWitness.toFocus.holeRels arity,
      outputLeaf.binders
          (layout.binderRegion
            (patternLeaf.binderEnumeration.binder relation.index)) =
        some ⟨arity, target⟩ := by
  let binder := patternLeaf.binderEnumeration.binder relation.index
  obtain ⟨parent, hbubble⟩ :=
    patternLeaf.binderEnumeration.bubble relation.index
  have hbubbleArity : input.pattern.val.diagram.regions binder =
      .bubble parent arity := by
    simpa only [binder, relation.hasArity] using hbubble
  obtain ⟨plugParent, htargetBubble⟩ :=
    layout.plugRaw_binderRegion_isBubble hadmissible binder parent arity
      hbubbleArity
  have hsourceEncloses : input.pattern.val.diagram.Encloses binder
      input.binderSpine.bodyContainer := by
    exact patternLeaf.binderEnumeration.encloses relation.index
  have hneRoot : binder ≠ input.pattern.val.diagram.root := by
    intro hroot
    rw [hroot, input.pattern.property.diagram_well_formed.root_is_sheet]
      at hbubbleArity
    contradiction
  have htargetEncloses : layout.plugRaw.Encloses
      (layout.binderRegion binder) (layout.frameRegion input.site) := by
    rcases material_or_proxy_of_ne_root input binder hneRoot with
      hmaterial | ⟨proxy, hproxy⟩
    · exact False.elim
        (layout.material_not_encloses_bodyContainer binder hmaterial
          hsourceEncloses)
    · rw [hproxy, layout.binderRegion_proxy]
      exact layout.frame_encloses
        (hadmissible.binder_targets_enclose proxy)
  exact outputLeaf.bindersCover _ plugParent arity htargetBubble
    htargetEncloses

/-- Relation transport for terminal pattern material, determined by concrete
binder ownership and the admissible proxy-to-host assignment. -/
noncomputable def patternRelationRenaming
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    RelationRenaming patternWitness.toFocus.holeRels
      outputWitness.toFocus.holeRels :=
  fun relation => Classical.choose
    (layout.patternRelationTarget_exists hadmissible patternWitness patternLeaf
      outputWitness outputLeaf relation)

theorem patternRelationRenaming_lookup
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {arity : Nat}
    (relation : Theory.RelVar patternWitness.toFocus.holeRels arity) :
    outputLeaf.binders
        (layout.binderRegion
          (patternLeaf.binderEnumeration.binder relation.index)) =
      some ⟨arity,
        layout.patternRelationRenaming hadmissible patternWitness patternLeaf
          outputWitness outputLeaf relation⟩ := by
  exact Classical.choose_spec
    (layout.patternRelationTarget_exists hadmissible patternWitness patternLeaf
      outputWitness outputLeaf relation)

theorem terminalBodyBinder_is_proxy
    (layout : PlugLayout input)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin patternWitness.toFocus.holeRels.length) :
    ∃ proxy : Fin input.binderSpine.proxyCount,
      patternLeaf.binderEnumeration.binder index =
        input.binderSpine.proxy proxy := by
  have hbody := input.binderSpine.body_eq_terminal_of_nonempty hnonempty
  change input.binderSpine.bodyContainer =
    input.binderSpine.proxy (input.terminalProxy hnonempty) at hbody
  have hencloses := patternLeaf.binderEnumeration.encloses index
  have hterminalEncloses : input.pattern.val.diagram.Encloses
      (patternLeaf.binderEnumeration.binder index)
      (input.binderSpine.proxy (input.terminalProxy hnonempty)) := by
    simpa only [← hbody] using hencloses
  rcases BinderSpine.enclosing_proxy_is_root_or_proxy input.pattern
      input.binderSpine (input.terminalProxy hnonempty) hterminalEncloses with
    hroot | ⟨proxy, _, hproxy⟩
  · obtain ⟨parent, hbubble⟩ := patternLeaf.binderEnumeration.bubble index
    rw [hroot, input.pattern.property.diagram_well_formed.root_is_sheet]
      at hbubble
    contradiction
  · exact ⟨proxy, hproxy⟩

theorem terminalBody_inherited_mem_iff_exposed
    (layout : PlugLayout input)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    wire ∈ patternLeaf.inheritedWires ↔
      wire ∈ input.pattern.val.exposedWires := by
  have hbody := input.binderSpine.body_eq_terminal_of_nonempty hnonempty
  change input.binderSpine.bodyContainer =
    input.binderSpine.proxy (input.terminalProxy hnonempty) at hbody
  have extendedNodup := patternLeaf.wiresExact.nodup
  rw [ConcreteElaboration.WireContext.extend,
    List.nodup_append] at extendedNodup
  have notLocal : wire ∈ patternLeaf.inheritedWires →
      (input.pattern.val.diagram.wires wire).scope ≠
        input.binderSpine.bodyContainer := by
    intro hinherited hscope
    have hlocal : wire ∈ ConcreteElaboration.exactScopeWires
        input.pattern.val.diagram input.binderSpine.bodyContainer :=
      (ConcreteElaboration.mem_exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer wire).2 hscope
    exact extendedNodup.2.2 wire hinherited wire hlocal rfl
  constructor
  · intro hinherited
    have hextended : wire ∈ patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer :=
      List.mem_append_left _ hinherited
    have hencloses : input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires wire).scope
        input.binderSpine.bodyContainer :=
      (patternLeaf.wiresExact.mem_iff wire).1 hextended
    have hterminalEncloses : input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires wire).scope
        (input.binderSpine.proxy (input.terminalProxy hnonempty)) := by
      simpa only [← hbody] using hencloses
    rcases BinderSpine.enclosing_proxy_is_root_or_proxy input.pattern
        input.binderSpine (input.terminalProxy hnonempty) hterminalEncloses with
      hroot | ⟨prior, hle, hscope⟩
    · by_cases hexposed : wire ∈ input.pattern.val.exposedWires
      · exact hexposed
      · have hhidden : wire ∈ input.pattern.val.hiddenWires :=
          (OpenConcreteDiagram.mem_hiddenWires input.pattern.val wire).2
            ⟨hroot, hexposed⟩
        rw [BinderSpine.TerminalBodyContract.hiddenWires_eq_nil_of_nonempty
          input.terminalBody hnonempty]
          at hhidden
        contradiction
    · by_cases heq : prior.val = (input.terminalProxy hnonempty).val
      · have priorEq : prior = input.terminalProxy hnonempty := Fin.ext heq
        subst prior
        exact False.elim ((notLocal hinherited) (hscope.trans hbody.symm))
      · have hnonterminal : prior.val + 1 < input.binderSpine.proxyCount := by
          omega
        by_cases hboundary : wire ∈ input.pattern.val.boundary
        · have rootScope := input.terminalBody.boundary_is_root_scoped wire
            hboundary
          exact False.elim (input.binderSpine.proxy_ne_root prior
            (hscope.symm.trans rootScope))
        · exact False.elim
            (input.terminalBody.nonterminal_has_no_nonboundary_wires prior
              hnonterminal wire hboundary hscope)
  · intro hexposed
    have rootScope := input.pattern.property.boundary_is_root_scoped wire
      ((OpenConcreteDiagram.mem_exposedWires input.pattern.val wire).1 hexposed)
    have rootEncloses : input.pattern.val.diagram.Encloses
        input.pattern.val.diagram.root input.binderSpine.bodyContainer :=
      input.pattern.property.diagram_well_formed.all_regions_reach_root
        input.binderSpine.bodyContainer
    have hextended : wire ∈ patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer :=
      (patternLeaf.wiresExact.mem_iff wire).2
        (by simpa [rootScope] using rootEncloses)
    rw [ConcreteElaboration.WireContext.extend, List.mem_append] at hextended
    rcases hextended with hinherited | hlocal
    · exact hinherited
    · have localScope :=
        (ConcreteElaboration.mem_exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer wire).1 hlocal
      exact False.elim (input.binderSpine.proxy_ne_root
        (input.terminalProxy hnonempty)
        (hbody.symm.trans (localScope.symm.trans rootScope)))

/-- Pattern inherited wires substituted into the complete coalesced-host site
context.  This is the wire component of the intrinsic splice kernel. -/
noncomputable def bodyTerminalWireRenaming
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Fin patternLeaf.inheritedWires.length →
      Fin (host.compilerLeaf.inheritedWires.extend input.site).length :=
  fun index =>
    let wire := patternLeaf.inheritedWires.get index
    let external := exposedWireIndex input wire
      ((layout.terminalBody_inherited_mem_iff_exposed patternWitness patternLeaf
        hnonempty wire).1 (List.get_mem _ index))
    layout.exposedWireRenaming hadmissible host external

theorem bodyTerminalWireRenaming_spec
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin patternLeaf.inheritedWires.length) :
    (host.compilerLeaf.inheritedWires.extend input.site).get
        (layout.bodyTerminalWireRenaming hadmissible host patternWitness
          patternLeaf hnonempty index) =
      layout.exposedAttachment
        (exposedWireIndex input (patternLeaf.inheritedWires.get index)
          ((layout.terminalBody_inherited_mem_iff_exposed patternWitness
            patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
            (List.get_mem _ index))) := by
  exact layout.exposedWireRenaming_spec hadmissible host _

theorem patternPlugWire_terminal_inherited
    (layout : PlugLayout input)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin patternLeaf.inheritedWires.length) :
    layout.patternPlugWire (patternLeaf.inheritedWires.get index) =
      layout.frameWire
        (layout.exposedAttachment
          (exposedWireIndex input (patternLeaf.inheritedWires.get index)
            ((layout.terminalBody_inherited_mem_iff_exposed patternWitness
              patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
              (List.get_mem _ index)))) := by
  let hexposed :=
    (layout.terminalBody_inherited_mem_iff_exposed patternWitness patternLeaf
      hnonempty (patternLeaf.inheritedWires.get index)).1
      (List.get_mem _ index)
  rw [layout.patternPlugWire_exposed _ hexposed]
  rfl

theorem patternPlugWire_terminal_local
    (layout : PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    layout.patternPlugWire
        ((ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).get index) =
      layout.internalWire
        (layout.bodyInternalCarriers.get
          ((layout.bodyInternalExactEquiv hnonempty).symm index)) := by
  let carrier := (layout.bodyInternalExactEquiv hnonempty).symm index
  let internal := layout.bodyInternalCarriers.get carrier
  have horigin := layout.bodyInternalExactEquiv_spec hnonempty carrier
  have hcarrier : layout.bodyInternalExactEquiv hnonempty carrier = index :=
    (layout.bodyInternalExactEquiv hnonempty).right_inv index
  have hinternal : layout.internalWires.origin internal ∉
      input.pattern.val.exposedWires :=
    (layout.internalWires_survives_iff
      (layout.internalWires.origin internal)).1
      (layout.internalWires.origin_survives internal)
  calc
    layout.patternPlugWire
        ((ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).get index) =
      layout.patternPlugWire (layout.internalWires.origin internal) := by
        apply congrArg layout.patternPlugWire
        rw [hcarrier] at horigin
        simpa [internal] using horigin
    _ = layout.internalBlockWire internal := by
      rw [layout.patternPlugWire_internal _ hinternal]
      apply congrArg layout.internalBlockWire
      exact layout.internalWires.index_origin internal
    _ = layout.internalWire internal := rfl

noncomputable def siteCombinedWireEquivOfNonempty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    FiniteEquiv
      (Fin (host.compilerLeaf.inheritedWires.length +
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length)))
      (Fin (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)) :=
  extendWireEquiv
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      (outputWitness := outputWitness) (outputLeaf := outputLeaf))
    (layout.siteLocalWireEquivOfNonempty hnonempty)

noncomputable def hostSeamPreparedWireOfNonempty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site) :
    Fin (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin (host.compilerLeaf.inheritedWires.length +
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length)) :=
  fun index =>
    Region.adjoinHostWire host.compilerLeaf.inheritedWires.length
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          host.compilerLeaf.inheritedWires input.site) index)

noncomputable def hostSeamWireMapOfNonempty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Fin (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
        outputLeaf hnonempty
        (layout.hostSeamPreparedWireOfNonempty hadmissible host index))

theorem hostSeamWireMapOfNonempty_spec
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (host.compilerLeaf.inheritedWires.extend input.site).length) :
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)).get
        (layout.hostSeamWireMapOfNonempty hadmissible host outputWitness
          outputLeaf hnonempty index) =
      layout.frameWire
        ((host.compilerLeaf.inheritedWires.extend input.site).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires input.site) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site).symm split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : layout.hostSeamWireMapOfNonempty hadmissible host
          outputWitness outputLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires
                (input.coalesceFrame hadmissible).val
                input.site).length outer)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion input.site)).length
            (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf outer)) := by
      have hprepared : Region.adjoinHostWire
          host.compilerLeaf.inheritedWires.length
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend
                host.compilerLeaf.inheritedWires input.site).symm
              (Fin.castAdd
                (ConcreteElaboration.exactScopeWires
                  (input.coalesceFrame hadmissible).val input.site).length
                outer))) =
        Fin.castAdd
          ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length +
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length) outer := by
        apply Fin.ext
        rfl
      apply Fin.ext
      simp only [hostSeamWireMapOfNonempty,
        hostSeamPreparedWireOfNonempty]
      rw [hprepared]
      simp [siteCombinedWireEquivOfNonempty, extendWireEquiv]
    rw [hmap]
    simpa only [ConcreteElaboration.WireContext.extend_get_outer] using
      layout.inheritedWireEquiv_spec host.intrinsicPath host.compilerLeaf
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) outer
  · have hmap : layout.hostSeamWireMapOfNonempty hadmissible host
          outputWitness outputLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site).symm
            (Fin.natAdd host.compilerLeaf.inheritedWires.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
          (Fin.natAdd outputLeaf.inheritedWires.length
            (layout.siteLocalWireEquivOfNonempty hnonempty
              (Fin.castAdd
                (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                  input.binderSpine.bodyContainer).length localIndex))) := by
      have hprepared : Region.adjoinHostWire
          host.compilerLeaf.inheritedWires.length
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend
                host.compilerLeaf.inheritedWires input.site).symm
              (Fin.natAdd host.compilerLeaf.inheritedWires.length
                localIndex))) =
        Fin.natAdd host.compilerLeaf.inheritedWires.length
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length localIndex) := by
        apply Fin.ext
        rfl
      let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
        outputWitness outputLeaf hnonempty
      let targetCast := Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      calc
        _ = targetCast (combined
            (Fin.natAdd host.compilerLeaf.inheritedWires.length
              (Fin.castAdd
                (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                  input.binderSpine.bodyContainer).length localIndex))) :=
          congrArg (fun prepared => targetCast (combined prepared)) hprepared
        _ = _ := by
          change targetCast
              (extendWireEquiv
                (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
                  outputWitness outputLeaf)
                (layout.siteLocalWireEquivOfNonempty hnonempty)
                (Fin.natAdd host.compilerLeaf.inheritedWires.length
                  (Fin.castAdd
                    (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                      input.binderSpine.bodyContainer).length localIndex))) =
            targetCast
              (Fin.natAdd outputLeaf.inheritedWires.length
                (layout.siteLocalWireEquivOfNonempty hnonempty
                  (Fin.castAdd
                    (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                      input.binderSpine.bodyContainer).length localIndex)))
          exact congrArg targetCast
            (extendWireEquiv_local
              (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
                outputWitness outputLeaf)
              (layout.siteLocalWireEquivOfNonempty hnonempty)
              (Fin.castAdd
                (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                  input.binderSpine.bodyContainer).length localIndex))
    rw [hmap]
    simpa only [ConcreteElaboration.WireContext.extend_get_local] using
      layout.siteLocalWireEquivOfNonempty_host_spec hnonempty localIndex

theorem hostSeamWireMapOfNonempty_eq
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    layout.hostSeamWireMapOfNonempty hadmissible host outputWitness outputLeaf
        hnonempty =
      layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf := by
  funext index
  apply Fin.ext
  apply (List.getElem_inj outputLeaf.wiresExact.nodup).mp
  have hvalues :=
    (layout.hostSeamWireMapOfNonempty_spec hadmissible host outputWitness
      outputLeaf hnonempty index).trans
      (layout.hostSiteWireIndexMap_spec host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf index).symm
  simpa only [List.get_eq_getElem] using hvalues

noncomputable def patternSeamPreparedWireOfNonempty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Fin (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length →
      Fin (host.compilerLeaf.inheritedWires.length +
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length)) :=
  fun index =>
    Region.adjoinMaterialWire
      host.compilerLeaf.inheritedWires.length
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length
      (Fin.cast
        (congrArg
          (fun length => length +
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length)
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (extendWireRenaming
          (layout.bodyTerminalWireRenaming hadmissible host patternWitness
            patternLeaf hnonempty)
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              patternLeaf.inheritedWires input.binderSpine.bodyContainer)
            index)))

noncomputable def patternSeamWireMapOfNonempty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    Fin (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
        outputLeaf hnonempty
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty index))

theorem patternSeamWireMapOfNonempty_spec
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (patternLeaf.inheritedWires.extend
      input.binderSpine.bodyContainer).length) :
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)).get
        (layout.patternSeamWireMapOfNonempty hadmissible host patternWitness
          patternLeaf outputWitness outputLeaf hnonempty index) =
      layout.patternPlugWire
        ((patternLeaf.inheritedWires.extend
          input.binderSpine.bodyContainer).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend
      patternLeaf.inheritedWires input.binderSpine.bodyContainer) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
        split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have hprepared : layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              patternLeaf.inheritedWires
              input.binderSpine.bodyContainer).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                input.binderSpine.bodyContainer).length inherited)) =
        Region.adjoinHostWire
          host.compilerLeaf.inheritedWires.length
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.bodyTerminalWireRenaming hadmissible host patternWitness
              patternLeaf hnonempty inherited)) := by
      apply Fin.ext
      simp [patternSeamPreparedWireOfNonempty, extendWireRenaming,
        Region.adjoinMaterialWire, Region.adjoinHostWire]
    have hmap : layout.patternSeamWireMapOfNonempty hadmissible host
          patternWitness patternLeaf outputWitness outputLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              patternLeaf.inheritedWires
              input.binderSpine.bodyContainer).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                input.binderSpine.bodyContainer).length inherited)) =
        layout.hostSeamWireMapOfNonempty hadmissible host outputWitness
          outputLeaf hnonempty
          (layout.bodyTerminalWireRenaming hadmissible host patternWitness
            patternLeaf hnonempty inherited) := by
      unfold patternSeamWireMapOfNonempty hostSeamWireMapOfNonempty
      unfold hostSeamPreparedWireOfNonempty
      exact congrArg
        (fun prepared =>
          Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              outputLeaf.inheritedWires
              (layout.frameRegion input.site)).symm
            (layout.siteCombinedWireEquivOfNonempty hadmissible host
              outputWitness outputLeaf hnonempty prepared))
        hprepared
    rw [hmap,
      layout.hostSeamWireMapOfNonempty_spec hadmissible host outputWitness
        outputLeaf hnonempty]
    rw [layout.bodyTerminalWireRenaming_spec hadmissible host patternWitness
      patternLeaf hnonempty]
    simpa only [ConcreteElaboration.WireContext.extend_get_outer] using
      (layout.patternPlugWire_terminal_inherited patternWitness patternLeaf
        hnonempty inherited).symm
  · have hprepared : layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              patternLeaf.inheritedWires
              input.binderSpine.bodyContainer).symm
            (Fin.natAdd patternLeaf.inheritedWires.length localIndex)) =
        Fin.natAdd host.compilerLeaf.inheritedWires.length
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length localIndex) := by
      apply Fin.ext
      have hhostLength :
          (host.compilerLeaf.inheritedWires.extend input.site).length =
            host.compilerLeaf.inheritedWires.length +
              (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                input.site).length := by
        simpa only [Input.coalesceFrame] using
          (ConcreteElaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site)
      simp [patternSeamPreparedWireOfNonempty, extendWireRenaming,
        Region.adjoinMaterialWire, Input.coalesceFrame]
      exact (congrArg (fun length => length + localIndex.val)
        hhostLength).trans (Nat.add_assoc _ _ _)
    let targetCast := Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
    have hmap : layout.patternSeamWireMapOfNonempty hadmissible host
          patternWitness patternLeaf outputWitness outputLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              patternLeaf.inheritedWires
              input.binderSpine.bodyContainer).symm
            (Fin.natAdd patternLeaf.inheritedWires.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
          (Fin.natAdd outputLeaf.inheritedWires.length
            (layout.siteLocalWireEquivOfNonempty hnonempty
              (Fin.natAdd
                (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                  input.site).length localIndex))) := by
      calc
        _ = targetCast
            (layout.siteCombinedWireEquivOfNonempty hadmissible host
              outputWitness outputLeaf hnonempty
              (Fin.natAdd host.compilerLeaf.inheritedWires.length
                (Fin.natAdd
                  (ConcreteElaboration.exactScopeWires
                    input.coalesceFrameRaw input.site).length localIndex))) :=
          congrArg
            (fun prepared => targetCast
              (layout.siteCombinedWireEquivOfNonempty hadmissible host
                outputWitness outputLeaf hnonempty prepared)) hprepared
        _ = _ := by
          change targetCast
              (extendWireEquiv
                (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
                  outputWitness outputLeaf)
                (layout.siteLocalWireEquivOfNonempty hnonempty)
                (Fin.natAdd host.compilerLeaf.inheritedWires.length
                  (Fin.natAdd
                    (ConcreteElaboration.exactScopeWires
                      input.coalesceFrameRaw input.site).length localIndex))) =
            targetCast
              (Fin.natAdd outputLeaf.inheritedWires.length
                (layout.siteLocalWireEquivOfNonempty hnonempty
                  (Fin.natAdd
                    (ConcreteElaboration.exactScopeWires
                      input.coalesceFrameRaw input.site).length localIndex)))
          exact congrArg targetCast
            (extendWireEquiv_local
              (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
                outputWitness outputLeaf)
              (layout.siteLocalWireEquivOfNonempty hnonempty)
              (Fin.natAdd
                (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                  input.site).length localIndex))
    rw [hmap]
    rw [ConcreteElaboration.WireContext.extend_get_local]
    rw [layout.siteLocalWireEquivOfNonempty_pattern_spec hnonempty]
    simpa only [ConcreteElaboration.WireContext.extend_get_local] using
      (layout.patternPlugWire_terminal_local hnonempty localIndex).symm

theorem patternSeamWireMapOfNonempty_eq
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    layout.patternSeamWireMapOfNonempty hadmissible host patternWitness
        patternLeaf outputWitness outputLeaf hnonempty =
      layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
        outputWitness outputLeaf := by
  funext index
  apply Fin.ext
  apply (List.getElem_inj outputLeaf.wiresExact.nodup).mp
  have hvalues :=
    (layout.patternSeamWireMapOfNonempty_spec hadmissible host patternWitness
      patternLeaf outputWitness outputLeaf hnonempty index).trans
      (layout.patternSiteWireIndexMap_spec hadmissible patternWitness
        patternLeaf outputWitness outputLeaf index).symm
  simpa only [List.get_eq_getElem] using hvalues

noncomputable def terminalBinderTarget
    (layout : PlugLayout input)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (relation : Theory.RelVar patternWitness.toFocus.holeRels arity) :
    Fin input.coalesceFrameRaw.regionCount :=
  input.binderTarget (Classical.choose
    (layout.terminalBodyBinder_is_proxy patternWitness patternLeaf hnonempty
      relation.index))

theorem terminalBinderTarget_spec
    (layout : PlugLayout input)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (relation : Theory.RelVar patternWitness.toFocus.holeRels arity) :
    layout.binderRegion
        (patternLeaf.binderEnumeration.binder relation.index) =
      layout.frameRegion
        (layout.terminalBinderTarget patternWitness patternLeaf hnonempty
          relation) := by
  let proxy := Classical.choose
    (layout.terminalBodyBinder_is_proxy patternWitness patternLeaf hnonempty
      relation.index)
  have hproxy := Classical.choose_spec
    (layout.terminalBodyBinder_is_proxy patternWitness patternLeaf hnonempty
      relation.index)
  rw [hproxy, layout.binderRegion_proxy]
  rfl

private theorem coalescedTerminalRelationTarget_exists
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    {arity : Nat} (relation : Theory.RelVar patternWitness.toFocus.holeRels arity) :
    ∃ target : Theory.RelVar hostWitness.toFocus.holeRels arity,
      hostLeaf.binders
          (layout.terminalBinderTarget patternWitness patternLeaf hnonempty
            relation) =
        some ⟨arity, target⟩ := by
  let proxy := Classical.choose
    (layout.terminalBodyBinder_is_proxy patternWitness patternLeaf hnonempty
      relation.index)
  have hproxy := Classical.choose_spec
    (layout.terminalBodyBinder_is_proxy patternWitness patternLeaf hnonempty
      relation.index)
  obtain ⟨binderParent, hbinder⟩ :=
    patternLeaf.binderEnumeration.bubble relation.index
  rw [hproxy, input.binderSpine.proxy_region] at hbinder
  have harity : input.binderSpine.arity proxy = arity :=
    (CRegion.bubble.inj hbinder |>.2).trans relation.hasArity
  obtain ⟨parent, hbubble⟩ := hadmissible.binder_targets_match proxy
  have hencloses : input.coalesceFrameRaw.Encloses
      (input.binderTarget proxy) input.site :=
    (input.coalesceFrameRaw_encloses_iff _ _).2
      (hadmissible.binder_targets_enclose proxy)
  obtain ⟨target, hlookup⟩ := hostLeaf.bindersCover
    (input.binderTarget proxy) parent arity
    (by simpa [← harity] using hbubble) hencloses
  exact ⟨target, by simpa [terminalBinderTarget, proxy]⟩

/-- Capture-avoiding relation substitution from the terminal pattern focus
into the coalesced host focus.  Ownership is recovered from concrete proxy
identity, so the map is independent of de Bruijn enumeration choices. -/
noncomputable def coalescedTerminalRelationRenaming
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness) :
    (hnonempty : input.binderSpine.proxyCount ≠ 0) →
    RelationRenaming patternWitness.toFocus.holeRels
      hostWitness.toFocus.holeRels :=
  fun hnonempty {arity} relation => Classical.choose
    (layout.coalescedTerminalRelationTarget_exists hadmissible hostWitness
      hostLeaf patternWitness patternLeaf hnonempty relation)

theorem coalescedTerminalRelationRenaming_lookup
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    {arity : Nat} (relation : Theory.RelVar patternWitness.toFocus.holeRels arity) :
    hostLeaf.binders
        (layout.terminalBinderTarget patternWitness patternLeaf hnonempty
          relation) =
      some ⟨arity,
        layout.coalescedTerminalRelationRenaming hadmissible hostWitness hostLeaf
          patternWitness patternLeaf hnonempty relation⟩ := by
  exact Classical.choose_spec
    (layout.coalescedTerminalRelationTarget_exists hadmissible hostWitness
      hostLeaf patternWitness patternLeaf hnonempty relation)

theorem terminalRelationRenaming_factor
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    ((fun {arity} (relation : Theory.RelVar
        patternWitness.toFocus.holeRels arity) =>
      layout.hostRelationRenaming hostWitness hostLeaf outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible hostWitness
          hostLeaf patternWitness patternLeaf hnonempty relation)) :
      RelationRenaming patternWitness.toFocus.holeRels
        outputWitness.toFocus.holeRels) =
      ((fun {arity} (relation : Theory.RelVar
          patternWitness.toFocus.holeRels arity) =>
        layout.patternRelationRenaming hadmissible patternWitness patternLeaf
          outputWitness outputLeaf relation) :
        RelationRenaming patternWitness.toFocus.holeRels
          outputWitness.toFocus.holeRels) := by
  apply @funext
  intro arity
  funext relation
  let intermediate :=
    layout.coalescedTerminalRelationRenaming hadmissible hostWitness hostLeaf
      patternWitness patternLeaf hnonempty relation
  let left := layout.hostRelationRenaming hostWitness hostLeaf outputWitness
    outputLeaf intermediate
  let right := layout.patternRelationRenaming hadmissible patternWitness
    patternLeaf outputWitness outputLeaf relation
  change left = right
  have hintermediate := layout.coalescedTerminalRelationRenaming_lookup
    hadmissible hostWitness hostLeaf patternWitness patternLeaf hnonempty relation
  have howner := hostLeaf.binderEnumeration.lookup_owner intermediate
    hintermediate
  have hleft := layout.hostRelationRenaming_lookup hostWitness hostLeaf
    outputWitness outputLeaf intermediate
  rw [howner] at hleft
  have hright := layout.patternRelationRenaming_lookup hadmissible
    patternWitness patternLeaf outputWitness outputLeaf relation
  rw [layout.terminalBinderTarget_spec patternWitness patternLeaf hnonempty
    relation] at hright
  change outputLeaf.binders
      (layout.frameRegion
        (layout.terminalBinderTarget patternWitness patternLeaf hnonempty
          relation)) = some ⟨arity, left⟩ at hleft
  change outputLeaf.binders
      (layout.frameRegion
        (layout.terminalBinderTarget patternWitness patternLeaf hnonempty
          relation)) = some ⟨arity, right⟩ at hright
  have hsigma := Option.some.inj (hleft.symm.trans hright)
  have hindexVal : left.index.val = right.index.val :=
    congrArg (fun value : Sigma fun arity =>
      Theory.RelVar outputWitness.toFocus.holeRels arity =>
        value.2.index.val) hsigma
  have hindex : left.index = right.index := Fin.ext hindexVal
  rcases hleftValue : left with ⟨leftIndex, leftArity⟩
  rcases hrightValue : right with ⟨rightIndex, rightArity⟩
  rw [hleftValue, hrightValue] at hindex
  cases hindex
  rfl

/-- Canonical lexical index transport for an empty proxy spine, where the
pattern body is compiled by the open sheet-root kernel. -/
noncomputable def patternRootWireIndexMap
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hzero : input.binderSpine.proxyCount = 0)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Fin (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    let wire := (input.pattern.val.exposedWires ++
      input.pattern.val.hiddenWires).get index
    outputLeaf.siteWireIndex outputWitness (layout.patternPlugWire wire)
      ((layout.patternPlugWire_visible_at_site_iff hadmissible wire).2 (by
        rw [input.binderSpine.body_eq_root_of_empty hzero]
        exact (openRootWires_exact input.pattern |>.mem_iff wire).1
          (List.get_mem _ index)))

theorem patternRootWireIndexMap_spec
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hzero : input.binderSpine.proxyCount = 0)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (index : Fin (input.pattern.val.exposedWires ++
      input.pattern.val.hiddenWires).length) :
    (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).get
        (layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf index) =
      layout.patternPlugWire
        ((input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).get index) := by
  unfold patternRootWireIndexMap
  exact outputLeaf.siteWireIndex_spec outputWitness _ _

theorem patternPlugWire_mem_outputRootContext_iff
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hzero : input.binderSpine.proxyCount = 0)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.patternPlugWire wire ∈
        outputLeaf.inheritedWires.extend (layout.frameRegion input.site) ↔
      wire ∈ input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires := by
  calc
    layout.patternPlugWire wire ∈ outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site) ↔
        layout.plugRaw.Encloses
          (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
          (layout.frameRegion input.site) :=
      outputLeaf.wiresExact.mem_iff (layout.patternPlugWire wire)
    _ ↔ input.pattern.val.diagram.Encloses
          (input.pattern.val.diagram.wires wire).scope
          input.binderSpine.bodyContainer :=
      layout.patternPlugWire_visible_at_site_iff hadmissible wire
    _ ↔ input.pattern.val.diagram.Encloses
          (input.pattern.val.diagram.wires wire).scope
          input.pattern.val.diagram.root := by
      rw [input.binderSpine.body_eq_root_of_empty hzero]
    _ ↔ wire ∈ input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires :=
      (openRootWires_exact input.pattern |>.mem_iff wire).symm

def emptyRelationRenaming (target : Theory.RelCtx) :
    RelationRenaming [] target :=
  fun relation => Fin.elim0 relation.index

/-- The complete inherited/local wire equivalence at an empty-spine splice.
The material-local block is the open pattern's hidden root wires. -/
noncomputable def siteCombinedWireEquivOfEmpty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0) :
    FiniteEquiv
      (Fin (host.compilerLeaf.inheritedWires.length +
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length + input.pattern.val.hiddenWires.length)))
      (Fin (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)) :=
  extendWireEquiv
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf)
    (layout.siteLocalWireEquivOfEmpty hzero)

noncomputable def hostSeamPreparedWireOfEmpty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site) :
    Fin (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin (host.compilerLeaf.inheritedWires.length +
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length + input.pattern.val.hiddenWires.length)) :=
  fun index =>
    Region.adjoinHostWire host.compilerLeaf.inheritedWires.length
      (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length input.pattern.val.hiddenWires.length
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          host.compilerLeaf.inheritedWires input.site) index)

noncomputable def hostSeamWireMapOfEmpty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0) :
    Fin (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
        outputLeaf hzero
        (layout.hostSeamPreparedWireOfEmpty hadmissible host index))

theorem hostSeamWireMapOfEmpty_spec
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin (host.compilerLeaf.inheritedWires.extend input.site).length) :
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)).get
        (layout.hostSeamWireMapOfEmpty hadmissible host outputWitness
          outputLeaf hzero index) =
      layout.frameWire
        ((host.compilerLeaf.inheritedWires.extend input.site).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires input.site) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site).symm split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : layout.hostSeamWireMapOfEmpty hadmissible host
          outputWitness outputLeaf hzero
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires
                (input.coalesceFrame hadmissible).val input.site).length
              outer)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion input.site)).length
            (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf outer)) := by
      have hprepared :
          layout.hostSeamPreparedWireOfEmpty hadmissible host
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend
                host.compilerLeaf.inheritedWires input.site).symm
              (Fin.castAdd
                (ConcreteElaboration.exactScopeWires
                  (input.coalesceFrame hadmissible).val input.site).length
                outer)) =
            Fin.castAdd
              ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                  input.site).length + input.pattern.val.hiddenWires.length)
              outer := by
        apply Fin.ext
        rfl
      let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
        outputWitness outputLeaf hzero
      let targetCast := Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      calc
        _ = targetCast (combined
            (Fin.castAdd
              ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                  input.site).length + input.pattern.val.hiddenWires.length)
              outer)) := congrArg (fun prepared => targetCast (combined prepared))
            hprepared
        _ = _ := congrArg targetCast
          (extendWireEquiv_outer
            (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf)
            (layout.siteLocalWireEquivOfEmpty hzero) outer)
    rw [hmap]
    simpa only [ConcreteElaboration.WireContext.extend_get_outer] using
      layout.inheritedWireEquiv_spec host.intrinsicPath host.compilerLeaf
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) outer
  · have hmap : layout.hostSeamWireMapOfEmpty hadmissible host
          outputWitness outputLeaf hzero
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site).symm
            (Fin.natAdd host.compilerLeaf.inheritedWires.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
          (Fin.natAdd outputLeaf.inheritedWires.length
            (layout.siteLocalWireEquivOfEmpty hzero
              (Fin.castAdd input.pattern.val.hiddenWires.length
                localIndex))) := by
      have hprepared :
          layout.hostSeamPreparedWireOfEmpty hadmissible host
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend
                host.compilerLeaf.inheritedWires input.site).symm
              (Fin.natAdd host.compilerLeaf.inheritedWires.length
                localIndex)) =
            Fin.natAdd host.compilerLeaf.inheritedWires.length
              (Fin.castAdd input.pattern.val.hiddenWires.length
                localIndex) := by
        apply Fin.ext
        rfl
      let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
        outputWitness outputLeaf hzero
      let targetCast := Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      calc
        _ = targetCast (combined
            (Fin.natAdd host.compilerLeaf.inheritedWires.length
              (Fin.castAdd input.pattern.val.hiddenWires.length
                localIndex))) := congrArg
                  (fun prepared => targetCast (combined prepared)) hprepared
        _ = _ := congrArg targetCast
          (extendWireEquiv_local
            (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf)
            (layout.siteLocalWireEquivOfEmpty hzero)
            (Fin.castAdd input.pattern.val.hiddenWires.length localIndex))
    rw [hmap]
    simpa only [ConcreteElaboration.WireContext.extend_get_local] using
      layout.siteLocalWireEquivOfEmpty_host_spec hzero localIndex

theorem hostSeamWireMapOfEmpty_eq
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0) :
    layout.hostSeamWireMapOfEmpty hadmissible host outputWitness outputLeaf
        hzero =
      layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf := by
  funext index
  apply Fin.ext
  apply (List.getElem_inj outputLeaf.wiresExact.nodup).mp
  have hvalues :=
    (layout.hostSeamWireMapOfEmpty_spec hadmissible host outputWitness
      outputLeaf hzero index).trans
      (layout.hostSiteWireIndexMap_spec host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf index).symm
  simpa only [List.get_eq_getElem] using hvalues

noncomputable def patternRootSeamPreparedWireOfEmpty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site) :
    Fin (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length →
      Fin (host.compilerLeaf.inheritedWires.length +
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length + input.pattern.val.hiddenWires.length)) :=
  fun index =>
    Fin.addCases
      (fun exposed => layout.hostSeamPreparedWireOfEmpty hadmissible host
        (layout.exposedWireRenaming hadmissible host exposed))
      (fun hidden =>
        Fin.natAdd host.compilerLeaf.inheritedWires.length
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length hidden))
      (Fin.cast
        (by simp) index)

noncomputable def patternRootSeamWireMapOfEmpty
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0) :
    Fin (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
      (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
        outputLeaf hzero
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host index))

theorem patternRootSeamWireMapOfEmpty_spec
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin (input.pattern.val.exposedWires ++
      input.pattern.val.hiddenWires).length) :
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site)).get
        (layout.patternRootSeamWireMapOfEmpty hadmissible host outputWitness
          outputLeaf hzero index) =
      layout.patternPlugWire
        ((input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).get index) := by
  let split : Fin (input.pattern.val.exposedWires.length +
      input.pattern.val.hiddenWires.length) := Fin.cast
    (by simp) index
  have hrecover : Fin.cast
      (by simp) split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · have hmap :
        layout.patternRootSeamWireMapOfEmpty hadmissible host outputWitness
          outputLeaf hzero
          (Fin.cast
            (by simp)
            (Fin.castAdd input.pattern.val.hiddenWires.length exposed)) =
        layout.hostSeamWireMapOfEmpty hadmissible host outputWitness
          outputLeaf hzero
          (layout.exposedWireRenaming hadmissible host exposed) := by
      apply Fin.ext
      simp [patternRootSeamWireMapOfEmpty,
        patternRootSeamPreparedWireOfEmpty,
        hostSeamWireMapOfEmpty]
    rw [hmap, layout.hostSeamWireMapOfEmpty_spec hadmissible host
      outputWitness outputLeaf hzero]
    rw [layout.exposedWireRenaming_spec hadmissible host]
    have hexposed : input.pattern.val.exposedWires.get exposed ∈
        input.pattern.val.exposedWires := List.get_mem _ exposed
    have hplug := layout.patternPlugWire_exposed
      (input.pattern.val.exposedWires.get exposed) hexposed
    have hindex : exposedWireIndex input
        (input.pattern.val.exposedWires.get exposed) hexposed = exposed := by
      apply exposedWire_get_injective input
      simp only [exposedWireIndex_get]
    have hget :
        (input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).get
            (Fin.cast (by simp)
              (Fin.castAdd input.pattern.val.hiddenWires.length exposed)) =
          input.pattern.val.exposedWires.get exposed := by
      simp
    rw [hget]
    rw [hplug, hindex]
    rfl
  · have hmap :
        layout.patternRootSeamWireMapOfEmpty hadmissible host outputWitness
          outputLeaf hzero
          (Fin.cast
            (by simp)
            (Fin.natAdd input.pattern.val.exposedWires.length hidden)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)).symm
          (Fin.natAdd outputLeaf.inheritedWires.length
            (layout.siteLocalWireEquivOfEmpty hzero
              (Fin.natAdd
                (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
                  input.site).length hidden))) := by
      apply Fin.ext
      simp [patternRootSeamWireMapOfEmpty,
        patternRootSeamPreparedWireOfEmpty,
        siteCombinedWireEquivOfEmpty, extendWireEquiv]
    rw [hmap]
    rw [ConcreteElaboration.WireContext.extend_get_local]
    rw [layout.siteLocalWireEquivOfEmpty_pattern_spec hzero hidden]
    let carrier := (layout.bodyInternalHiddenEquiv hzero).symm hidden
    let internal := layout.bodyInternalCarriers.get carrier
    have horigin := layout.bodyInternalHiddenEquiv_spec hzero carrier
    have hcarrier : layout.bodyInternalHiddenEquiv hzero carrier = hidden :=
      (layout.bodyInternalHiddenEquiv hzero).right_inv hidden
    rw [hcarrier] at horigin
    have hhidden : input.pattern.val.hiddenWires.get hidden ∉
        input.pattern.val.exposedWires :=
      (OpenConcreteDiagram.mem_hiddenWires input.pattern.val
        (input.pattern.val.hiddenWires.get hidden)).1
        (List.get_mem _ hidden) |>.2
    have hsurvives : layout.internalWires.survives
        (input.pattern.val.hiddenWires.get hidden) = true :=
      (layout.internalWires_survives_iff
        (input.pattern.val.hiddenWires.get hidden)).2 hhidden
    have hget :
        (input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).get
            (Fin.cast (by simp)
              (Fin.natAdd input.pattern.val.exposedWires.length hidden)) =
          input.pattern.val.hiddenWires.get hidden := by
      simp
    rw [hget, layout.patternPlugWire_internal _ hhidden]
    apply congrArg layout.internalBlockWire
    apply layout.internalWires.origin_injective
    calc
      layout.internalWires.origin
          (layout.bodyInternalCarriers.get carrier) =
          input.pattern.val.hiddenWires.get hidden := by
        simpa [internal] using horigin.symm
      _ = layout.internalWires.origin
          (layout.internalWires.index
            (input.pattern.val.hiddenWires.get hidden) hsurvives) :=
        (layout.internalWires.origin_index _ _).symm

theorem patternRootSeamWireMapOfEmpty_eq
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0) :
    layout.patternRootSeamWireMapOfEmpty hadmissible host outputWitness
        outputLeaf hzero =
      layout.patternRootWireIndexMap hadmissible hzero outputWitness
        outputLeaf := by
  funext index
  apply Fin.ext
  apply (List.getElem_inj outputLeaf.wiresExact.nodup).mp
  have hvalues :=
    (layout.patternRootSeamWireMapOfEmpty_spec hadmissible host outputWitness
      outputLeaf hzero index).trans
      (layout.patternRootWireIndexMap_spec hadmissible hzero outputWitness
        outputLeaf index).symm
  simpa only [List.get_eq_getElem] using hvalues

/-- Exact wire-index transport at an arbitrary retained material region. -/
noncomputable def patternMaterialWireIndexMap
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.bodyRegion region)) :
    Fin sourceContext.length → Fin targetContext.length :=
  fun index =>
    let wire := sourceContext.get index
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((targetExact.mem_iff (layout.patternPlugWire wire)).2
        ((layout.patternPlugWire_visible_at_material_iff hadmissible region
          hregion wire).2
          ((sourceExact.mem_iff wire).1 (List.get_mem _ index)))))

theorem patternMaterialWireIndexMap_spec
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.bodyRegion region))
    (index : Fin sourceContext.length) :
    targetContext.get
        (layout.patternMaterialWireIndexMap hadmissible region hregion
          sourceContext targetContext sourceExact targetExact index) =
      layout.patternPlugWire (sourceContext.get index) := by
  apply ConcreteElaboration.WireContext.lookup?_sound
  exact Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
    ((targetExact.mem_iff
      (layout.patternPlugWire (sourceContext.get index))).2
      ((layout.patternPlugWire_visible_at_material_iff hadmissible region
        hregion (sourceContext.get index)).2
        ((sourceExact.mem_iff (sourceContext.get index)).1
          (List.get_mem _ index)))))

theorem patternMaterialWireIndexMap_eq
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.bodyRegion region))
    (map : Fin sourceContext.length → Fin targetContext.length)
    (hspec : ∀ index, targetContext.get (map index) =
      layout.patternPlugWire (sourceContext.get index)) :
    map = layout.patternMaterialWireIndexMap hadmissible region hregion
      sourceContext targetContext sourceExact targetExact := by
  funext index
  apply Fin.ext
  apply (List.getElem_inj targetExact.nodup).mp
  have hvalues := (hspec index).trans
    (layout.patternMaterialWireIndexMap_spec hadmissible region hregion
      sourceContext targetContext sourceExact targetExact index).symm
  simpa only [List.get_eq_getElem] using hvalues

theorem patternPlugWire_mem_materialContext_iff
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.bodyRegion region))
    (wire : Fin input.pattern.val.diagram.wireCount) :
    layout.patternPlugWire wire ∈ targetContext ↔ wire ∈ sourceContext := by
  calc
    layout.patternPlugWire wire ∈ targetContext ↔
        layout.plugRaw.Encloses
          (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
          (layout.bodyRegion region) :=
      targetExact.mem_iff (layout.patternPlugWire wire)
    _ ↔ input.pattern.val.diagram.Encloses
          (input.pattern.val.diagram.wires wire).scope region :=
      layout.patternPlugWire_visible_at_material_iff hadmissible region
        hregion wire
    _ ↔ wire ∈ sourceContext := (sourceExact.mem_iff wire).symm

private theorem patternMaterialRelationTarget_exists
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    ∃ target : Theory.RelVar targetRels arity,
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, target⟩ := by
  let binder := sourceEnumeration.binder relation.index
  obtain ⟨parent, hbubble⟩ := sourceEnumeration.bubble relation.index
  have hbubbleArity : input.pattern.val.diagram.regions binder =
      .bubble parent arity := by
    simpa only [binder, relation.hasArity] using hbubble
  obtain ⟨plugParent, htargetBubble⟩ :=
    layout.plugRaw_binderRegion_isBubble hadmissible binder parent arity
      hbubbleArity
  have hsourceEncloses : input.pattern.val.diagram.Encloses binder region :=
    sourceEnumeration.encloses relation.index
  have hneRoot : binder ≠ input.pattern.val.diagram.root := by
    intro hroot
    rw [hroot, input.pattern.property.diagram_well_formed.root_is_sheet]
      at hbubbleArity
    contradiction
  have htargetEncloses : layout.plugRaw.Encloses
      (layout.binderRegion binder) (layout.bodyRegion region) := by
    rcases material_or_proxy_of_ne_root input binder hneRoot with
      hmaterial | ⟨proxy, hproxy⟩
    · rw [layout.binderRegion_material binder hmaterial]
      exact layout.material_encloses hmaterial hregion hsourceEncloses
    · rw [hproxy, layout.binderRegion_proxy]
      exact layout.plugRaw_encloses_trans
        (layout.frame_encloses (hadmissible.binder_targets_enclose proxy))
        (layout.site_encloses_bodyRegion region)
  exact targetCover _ plugParent arity htargetBubble htargetEncloses

noncomputable def patternMaterialRelationRenaming
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region) :
    RelationRenaming sourceRels targetRels :=
  fun relation => Classical.choose
    (layout.patternMaterialRelationTarget_exists hadmissible region hregion
      sourceBinders targetBinders sourceCover targetCover sourceEnumeration
      relation)

theorem patternMaterialRelationRenaming_lookup
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    targetBinders
        (layout.binderRegion
          (sourceEnumeration.binder relation.index)) =
      some ⟨arity,
        layout.patternMaterialRelationRenaming hadmissible region hregion
          sourceBinders targetBinders sourceCover targetCover sourceEnumeration
          relation⟩ := by
  exact Classical.choose_spec
    (layout.patternMaterialRelationTarget_exists hadmissible region hregion
      sourceBinders targetBinders sourceCover targetCover sourceEnumeration
      relation)

theorem patternMaterialRelationRenaming_eq
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    (rho : RelationRenaming sourceRels targetRels)
    (hlookup : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, rho relation⟩)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    rho relation =
      layout.patternMaterialRelationRenaming hadmissible region hregion
        sourceBinders targetBinders sourceCover targetCover sourceEnumeration
        relation := by
  let canonical :=
    layout.patternMaterialRelationRenaming hadmissible region hregion
      sourceBinders targetBinders sourceCover targetCover sourceEnumeration
      relation
  change rho relation = canonical
  have hcanonical :=
    layout.patternMaterialRelationRenaming_lookup hadmissible region hregion
      sourceBinders targetBinders sourceCover targetCover sourceEnumeration
      relation
  change targetBinders
      (layout.binderRegion
        (sourceEnumeration.binder relation.index)) =
    some ⟨arity, canonical⟩ at hcanonical
  have hsigma := Option.some.inj ((hlookup relation).symm.trans hcanonical)
  have hindexVal : (rho relation).index.val = canonical.index.val :=
    congrArg (fun value : Sigma fun arity => Theory.RelVar targetRels arity =>
      value.2.index.val) hsigma
  have hindex : (rho relation).index = canonical.index := Fin.ext hindexVal
  rcases hleft : rho relation with ⟨leftIndex, leftArity⟩
  rcases hright : canonical with ⟨rightIndex, rightArity⟩
  rw [hleft, hright] at hindex
  cases hindex
  rfl

theorem binderRegion_ne_bodyRegion_directMaterialChild
    (layout : PlugLayout input)
    (parent child binder : Fin input.pattern.val.diagram.regionCount)
    (hchildMaterial : input.binderSpine.IsMaterialRegion child)
    (hparent : (input.pattern.val.diagram.regions child).parent? = some parent)
    (binderParent : Fin input.pattern.val.diagram.regionCount)
    (binderArity : Nat)
    (hbinder : input.pattern.val.diagram.regions binder =
      .bubble binderParent binderArity)
    (hencloses : input.pattern.val.diagram.Encloses binder parent) :
    layout.binderRegion binder ≠ layout.bodyRegion child := by
  have hbinderNeRoot : binder ≠ input.pattern.val.diagram.root := by
    intro heq
    rw [heq, input.pattern.property.diagram_well_formed.root_is_sheet]
      at hbinder
    contradiction
  rcases material_or_proxy_of_ne_root input binder hbinderNeRoot with
    hbinderMaterial | ⟨proxy, hproxy⟩
  · rw [layout.binderRegion_material binder hbinderMaterial]
    intro heq
    have hbinderEq := layout.bodyRegion_injective_of_material
      hbinderMaterial hchildMaterial heq
    subst binder
    exact ConcreteElaboration.checked_direct_child_not_encloses_parent
      input.pattern.property.diagram_well_formed hparent hencloses
  · rw [hproxy, layout.binderRegion_proxy,
      layout.bodyRegion_material child hchildMaterial]
    exact layout.frameRegion_ne_materialRegion _ _

/-- Distinct pattern binders cannot collide with the image of a retained
material region.  Material regions occupy the plug's material summand, while
the root and proxy binders occupy its retained-frame summand. -/
theorem binderRegion_ne_bodyRegion_of_ne_material
    (layout : PlugLayout input)
    (binder child : Fin input.pattern.val.diagram.regionCount)
    (hchildMaterial : input.binderSpine.IsMaterialRegion child)
    (hne : binder ≠ child) :
    layout.binderRegion binder ≠ layout.bodyRegion child := by
  by_cases hroot : binder = input.pattern.val.diagram.root
  · subst binder
    have hproxy : layout.proxyIndex? input.pattern.val.diagram.root = none := by
      unfold proxyIndex?
      cases hlookup : indexOf? layout.proxies
          input.pattern.val.diagram.root with
      | none => rfl
      | some found =>
          have hsound := indexOf?_sound hlookup
          have hmember : input.pattern.val.diagram.root ∈ layout.proxies := by
            rw [← hsound]
            exact List.get_mem _ _
          rw [proxies, List.mem_map] at hmember
          rcases hmember with ⟨proxy, _, equality⟩
          exact False.elim
            (input.binderSpine.proxy_ne_root proxy equality)
    rw [binderRegion, hproxy, layout.bodyRegion_root,
      layout.bodyRegion_material child hchildMaterial]
    exact layout.frameRegion_ne_materialRegion _ _
  · rcases material_or_proxy_of_ne_root input binder hroot with
      hbinderMaterial | ⟨proxy, hproxy⟩
    · rw [layout.binderRegion_material binder hbinderMaterial]
      intro equality
      exact hne (layout.bodyRegion_injective_of_material
        hbinderMaterial hchildMaterial equality)
    · rw [hproxy, layout.binderRegion_proxy,
        layout.bodyRegion_material child hchildMaterial]
      exact layout.frameRegion_ne_materialRegion _ _

/-- A heterogeneous binder-context witness for the intrinsic pattern and its
plug image.  The renaming is data, and `lookup` records that it follows the
actual concrete binder identities used by the compiler. -/
structure PatternBinderWitness
    (layout : PlugLayout input)
    {sourceRels targetRels : Theory.RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  lookup : ∀ (binder : Fin input.pattern.val.diagram.regionCount)
      {arity : Nat} (relation : Theory.RelVar sourceRels arity),
    sourceBinders binder = some ⟨arity, relation⟩ →
      targetBinders (layout.binderRegion binder) =
        some ⟨arity, relationMap relation⟩

namespace PatternBinderWitness

def empty (layout : PlugLayout input) :
    PatternBinderWitness layout
      ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty where
  relationMap := emptyRelationRenaming []
  lookup := by
    intro binder arity relation sourceLookup
    simp [ConcreteElaboration.BinderContext.empty] at sourceLookup

/-- At an intrinsic open root there are no source binders.  Therefore the
root witness embeds the empty source relation context into any surrounding
target relation context without imposing a target-binder restriction. -/
def root (layout : PlugLayout input)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels) :
    PatternBinderWitness layout
      ConcreteElaboration.BinderContext.empty targetBinders where
  relationMap := emptyRelationRenaming targetRels
  lookup := by
    intro binder arity relation sourceLookup
    simp [ConcreteElaboration.BinderContext.empty] at sourceLookup

noncomputable def pushMaterial
    (layout : PlugLayout input)
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels}
    (witness : PatternBinderWitness layout sourceBinders targetBinders)
    (child : Fin input.pattern.val.diagram.regionCount)
    (arity : Nat)
    (hchildMaterial : input.binderSpine.IsMaterialRegion child) :
    PatternBinderWitness layout
      (sourceBinders.push child arity)
      (targetBinders.push (layout.bodyRegion child) arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  lookup := by
    intro binder relationArity relation sourceLookup
    by_cases hbinder : binder = child
    · subst binder
      rw [ConcreteElaboration.BinderContext.push_self] at sourceLookup
      have payload := Option.some.inj sourceLookup
      cases payload
      rw [layout.binderRegion_material child hchildMaterial,
        ConcreteElaboration.BinderContext.push_self]
      rfl
    · rw [ConcreteElaboration.BinderContext.push_other sourceBinders arity
        hbinder] at sourceLookup
      cases hsource : sourceBinders binder with
      | none => simp [hsource] at sourceLookup
      | some payload =>
          rcases payload with ⟨sourceArity, sourceRelation⟩
          simp only [hsource, Option.map_some] at sourceLookup
          have targetNe := layout.binderRegion_ne_bodyRegion_of_ne_material
            binder child hchildMaterial hbinder
          rw [ConcreteElaboration.BinderContext.push_other targetBinders arity
            targetNe]
          rw [witness.lookup binder sourceRelation hsource]
          cases sourceLookup
          rfl

noncomputable def push
    (layout : PlugLayout input)
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels}
    (witness : PatternBinderWitness layout sourceBinders targetBinders)
    (child parent : Fin input.pattern.val.diagram.regionCount)
    (arity : Nat)
    (childKind : input.pattern.val.diagram.regions child =
      .bubble parent arity)
    (hparentMaterial : input.binderSpine.IsMaterialRegion parent) :
    PatternBinderWitness layout
      (sourceBinders.push child arity)
      (targetBinders.push (layout.bodyRegion child) arity) := by
  have childParent :
      (input.pattern.val.diagram.regions child).parent? = some parent := by
    simp [childKind, CRegion.parent?]
  have hchildMaterial := directChildOfMaterial_material input parent child
    hparentMaterial childParent
  exact pushMaterial layout witness child arity hchildMaterial

theorem relationMap_push
    (layout : PlugLayout input)
    {sourceRels targetRels : Theory.RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels}
    (witness : PatternBinderWitness layout sourceBinders targetBinders)
    (child parent : Fin input.pattern.val.diagram.regionCount)
    (arity : Nat)
    (childKind : input.pattern.val.diagram.regions child =
      .bubble parent arity)
    (hparentMaterial : input.binderSpine.IsMaterialRegion parent) :
    ((push layout witness child parent arity childKind
      hparentMaterial).relationMap :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := rfl

end PatternBinderWitness

theorem materialRelationLookup_cutChild
    (layout : PlugLayout input)
    (parent child : Fin input.pattern.val.diagram.regionCount)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders parent)
    (hchild : input.pattern.val.diagram.regions child = .cut parent)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    targetBinders
        (layout.binderRegion
          ((sourceEnumeration.cutChild
            input.pattern.property.diagram_well_formed hchild).binder
              relation.index)) =
      some ⟨arity, relationMap relation⟩ := by
  exact relationSpec relation

theorem materialRelationLookup_bubbleChild
    (layout : PlugLayout input)
    (parent child : Fin input.pattern.val.diagram.regionCount)
    (hparentMaterial : input.binderSpine.IsMaterialRegion parent)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders parent)
    (childArity : Nat)
    (hchild : input.pattern.val.diagram.regions child =
      .bubble parent childArity)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {arity : Nat} (relation : Theory.RelVar (childArity :: sourceRels) arity) :
    (targetBinders.push (layout.bodyRegion child) childArity)
        (layout.binderRegion
          ((sourceEnumeration.bubbleChild
            input.pattern.property.diagram_well_formed hchild).binder
              relation.index)) =
      some ⟨arity, RelationRenaming.lift relationMap childArity relation⟩ := by
  have hparent : (input.pattern.val.diagram.regions child).parent? =
      some parent := by simp [hchild, CRegion.parent?]
  have hchildMaterial := directChildOfMaterial_material input parent child
    hparentMaterial hparent
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro hasArity
    have harity : arity = childArity := by simpa using hasArity.symm
    subst arity
    change (targetBinders.push (layout.bodyRegion child) childArity)
        (layout.binderRegion child) =
      some ⟨childArity,
        RelationRenaming.lift relationMap childArity
          ⟨0, rfl⟩⟩
    rw [layout.binderRegion_material child hchildMaterial,
      ConcreteElaboration.BinderContext.push_self]
    rfl
  · intro hasArity
    let sourceRelation : Theory.RelVar sourceRels arity :=
      ⟨tail, by simpa using hasArity⟩
    obtain ⟨binderParent, hbinder⟩ := sourceEnumeration.bubble tail
    have hne := layout.binderRegion_ne_bodyRegion_directMaterialChild
      parent child (sourceEnumeration.binder tail) hchildMaterial hparent
      binderParent (sourceRels.get tail) hbinder
      (sourceEnumeration.encloses tail)
    change (targetBinders.push (layout.bodyRegion child) childArity)
        (layout.binderRegion (sourceEnumeration.binder tail)) =
      some ⟨arity,
        RelationRenaming.lift relationMap childArity
          ⟨tail.succ, hasArity⟩⟩
    rw [ConcreteElaboration.BinderContext.push_other targetBinders childArity hne,
      relationSpec sourceRelation]
    rfl

theorem frameRelationLookup_cutChild
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (parent child : Fin input.coalesceFrameRaw.regionCount)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders parent)
    (hchild : input.coalesceFrameRaw.regions child = .cut parent)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    targetBinders
        (layout.frameRegion
          ((sourceEnumeration.cutChild
            (input.coalesceFrameRaw_wellFormed hadmissible) hchild).binder
              relation.index)) =
      some ⟨arity, relationMap relation⟩ := by
  exact relationSpec relation

theorem frameRelationLookup_bubbleChild
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (parent child : Fin input.coalesceFrameRaw.regionCount)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders parent)
    (childArity : Nat)
    (hchild : input.coalesceFrameRaw.regions child =
      .bubble parent childArity)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {arity : Nat} (relation : Theory.RelVar (childArity :: sourceRels) arity) :
    (targetBinders.push (layout.frameRegion child) childArity)
        (layout.frameRegion
          ((sourceEnumeration.bubbleChild
            (input.coalesceFrameRaw_wellFormed hadmissible) hchild).binder
              relation.index)) =
      some ⟨arity, RelationRenaming.lift relationMap childArity relation⟩ := by
  have hparent : (input.coalesceFrameRaw.regions child).parent? =
      some parent := by
    change (input.frame.val.regions child).parent? = some parent
    change input.frame.val.regions child = .bubble parent childArity at hchild
    simp [hchild, CRegion.parent?]
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro hasArity
    have harity : arity = childArity := by simpa using hasArity.symm
    subst arity
    change (targetBinders.push (layout.frameRegion child) childArity)
        (layout.frameRegion child) =
      some ⟨childArity,
        RelationRenaming.lift relationMap childArity ⟨0, rfl⟩⟩
    rw [ConcreteElaboration.BinderContext.push_self]
    rfl
  · intro hasArity
    let sourceRelation : Theory.RelVar sourceRels arity :=
      ⟨tail, by simpa using hasArity⟩
    have hne : layout.frameRegion (sourceEnumeration.binder tail) ≠
        layout.frameRegion child := by
      intro heq
      have hsourceEq : sourceEnumeration.binder tail = child :=
        layout.frameRegion_injective heq
      exact ConcreteElaboration.checked_direct_child_not_encloses_parent
        (input.coalesceFrameRaw_wellFormed hadmissible) hparent
        (by simpa [hsourceEq] using sourceEnumeration.encloses tail)
    change (targetBinders.push (layout.frameRegion child) childArity)
        (layout.frameRegion (sourceEnumeration.binder tail)) =
      some ⟨arity,
        RelationRenaming.lift relationMap childArity
          ⟨tail.succ, hasArity⟩⟩
    rw [ConcreteElaboration.BinderContext.push_other targetBinders childArity hne,
      relationSpec sourceRelation]
    rfl

theorem plugRaw_endpoint_wire_unique (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    ∀ (first second : Fin layout.plugRaw.wireCount)
      (endpoint : CEndpoint layout.plugRaw.nodeCount),
      layout.plugRaw.EndpointOccurs first endpoint →
      layout.plugRaw.EndpointOccurs second endpoint →
      first = second := by
  let checkedPattern : CheckedDiagram signature :=
    ⟨input.pattern.val.diagram,
      input.pattern.property.diagram_well_formed⟩
  intro first
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count)
    (fun firstQuotient => ?_) (fun firstInternal => ?_) first
  · intro second
    refine Fin.addCases (m := input.wireQuotient.count)
      (n := layout.internalWires.count)
      (fun secondQuotient => ?_) (fun secondInternal => ?_) second
    · intro endpoint hfirst hsecond
      change CEndpoint layout.nodeCount at endpoint
      rcases quotient_endpoint_provenance signature input layout
          firstQuotient endpoint hfirst with
        ⟨firstFrame, hfirstOccurs, hfirstMap⟩ |
          ⟨firstExternal, hfirstAttachment, firstPattern,
            hfirstOccurs, hfirstMap⟩
      · rcases quotient_endpoint_provenance signature input layout
            secondQuotient endpoint hsecond with
          ⟨secondFrame, hsecondOccurs, hsecondMap⟩ |
            ⟨secondExternal, hsecondAttachment, secondPattern,
              hsecondOccurs, hsecondMap⟩
        · have horiginal := layout.mapFrameEndpoint_injective
              (hfirstMap.trans hsecondMap.symm)
          subst secondFrame
          have hquotient := checked_endpoint_wire_unique
            (input.coalesceFrame hadmissible)
            firstQuotient secondQuotient firstFrame
            hfirstOccurs hsecondOccurs
          exact congrArg layout.quotientBlockWire hquotient
        · exact False.elim
            (layout.mapFrameEndpoint_ne_mapPatternEndpoint
              firstFrame secondPattern (hfirstMap.trans hsecondMap.symm))
      · rcases quotient_endpoint_provenance signature input layout
            secondQuotient endpoint hsecond with
          ⟨secondFrame, hsecondOccurs, hsecondMap⟩ |
            ⟨secondExternal, hsecondAttachment, secondPattern,
              hsecondOccurs, hsecondMap⟩
        · exact False.elim
            (layout.mapFrameEndpoint_ne_mapPatternEndpoint
              secondFrame firstPattern (hsecondMap.trans hfirstMap.symm))
        · have horiginal := layout.mapPatternEndpoint_injective
              (hfirstMap.trans hsecondMap.symm)
          subst secondPattern
          have hwire := checked_endpoint_wire_unique checkedPattern
            (input.pattern.val.exposedWires.get firstExternal)
            (input.pattern.val.exposedWires.get secondExternal)
            firstPattern hfirstOccurs hsecondOccurs
          have hexternal := exposedWire_get_injective input hwire
          subst secondExternal
          have hquotient := hfirstAttachment.symm.trans hsecondAttachment
          exact congrArg layout.quotientBlockWire hquotient
    · intro endpoint hfirst hsecond
      change CEndpoint layout.nodeCount at endpoint
      rcases quotient_endpoint_provenance signature input layout
          firstQuotient endpoint hfirst with
        ⟨firstFrame, _, hfirstMap⟩ |
          ⟨firstExternal, _, firstPattern, hfirstOccurs, hfirstMap⟩
      · obtain ⟨secondPattern, _, hsecondMap⟩ :=
          internal_endpoint_provenance signature input layout
            secondInternal endpoint hsecond
        exact False.elim
          (layout.mapFrameEndpoint_ne_mapPatternEndpoint
            firstFrame secondPattern (hfirstMap.trans hsecondMap.symm))
      · obtain ⟨secondPattern, hsecondOccurs, hsecondMap⟩ :=
          internal_endpoint_provenance signature input layout
            secondInternal endpoint hsecond
        have horiginal := layout.mapPatternEndpoint_injective
          (hfirstMap.trans hsecondMap.symm)
        subst secondPattern
        have hwire := checked_endpoint_wire_unique checkedPattern
          (input.pattern.val.exposedWires.get firstExternal)
          (layout.internalWires.origin secondInternal)
          firstPattern hfirstOccurs hsecondOccurs
        have hinternal : layout.internalWires.origin secondInternal ∉
            input.pattern.val.exposedWires :=
          (layout.internalWires_survives_iff _).1
            (layout.internalWires.origin_survives secondInternal)
        exact False.elim (hinternal (by
          rw [← hwire]
          exact List.get_mem _ _))
  · intro second
    refine Fin.addCases (m := input.wireQuotient.count)
      (n := layout.internalWires.count)
      (fun secondQuotient => ?_) (fun secondInternal => ?_) second
    · intro endpoint hfirst hsecond
      change CEndpoint layout.nodeCount at endpoint
      obtain ⟨firstPattern, hfirstOccurs, hfirstMap⟩ :=
        internal_endpoint_provenance signature input layout
          firstInternal endpoint hfirst
      rcases quotient_endpoint_provenance signature input layout
          secondQuotient endpoint hsecond with
        ⟨secondFrame, _, hsecondMap⟩ |
          ⟨secondExternal, _, secondPattern, hsecondOccurs, hsecondMap⟩
      · exact False.elim
          (layout.mapFrameEndpoint_ne_mapPatternEndpoint
            secondFrame firstPattern (hsecondMap.trans hfirstMap.symm))
      · have horiginal := layout.mapPatternEndpoint_injective
            (hfirstMap.trans hsecondMap.symm)
        subst secondPattern
        have hwire := checked_endpoint_wire_unique checkedPattern
          (layout.internalWires.origin firstInternal)
          (input.pattern.val.exposedWires.get secondExternal)
          firstPattern hfirstOccurs hsecondOccurs
        have hinternal : layout.internalWires.origin firstInternal ∉
            input.pattern.val.exposedWires :=
          (layout.internalWires_survives_iff _).1
            (layout.internalWires.origin_survives firstInternal)
        exact False.elim (hinternal (by
          rw [hwire]
          exact List.get_mem _ _))
    · intro endpoint hfirst hsecond
      change CEndpoint layout.nodeCount at endpoint
      obtain ⟨firstPattern, hfirstOccurs, hfirstMap⟩ :=
        internal_endpoint_provenance signature input layout
          firstInternal endpoint hfirst
      obtain ⟨secondPattern, hsecondOccurs, hsecondMap⟩ :=
        internal_endpoint_provenance signature input layout
          secondInternal endpoint hsecond
      have horiginal := layout.mapPatternEndpoint_injective
        (hfirstMap.trans hsecondMap.symm)
      subst secondPattern
      have hwire := checked_endpoint_wire_unique checkedPattern
        (layout.internalWires.origin firstInternal)
        (layout.internalWires.origin secondInternal)
        firstPattern hfirstOccurs hsecondOccurs
      have hinternal := layout.internalWires.origin_injective hwire
      exact congrArg layout.internalBlockWire hinternal

theorem plugRaw_wire_endpoints_are_disjoint (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.WireEndpointsAreDisjoint := by
  intro first second hne endpoint hfirst
  by_cases hsecond : layout.plugRaw.EndpointOccurs second endpoint
  · have heq := layout.plugRaw_endpoint_wire_unique signature input
      hadmissible first second endpoint hfirst hsecond
    subst second
    change (!decide (first = first)) = true at hne
    simp at hne
  · change (!decide (layout.plugRaw.EndpointOccurs second endpoint)) = true
    rw [decide_eq_false_iff_not.mpr hsecond]
    rfl

/-- Plugging preserves every concrete well-formedness clause directly. -/
theorem plugRaw_wellFormed (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible) :
    layout.plugRaw.WellFormed signature where
  root_is_sheet := layout.plugRaw_root_is_sheet
  only_root_is_sheet := layout.plugRaw_only_root_is_sheet
  all_regions_reach_root := layout.plugRaw_all_regions_reach_root
  atom_binders_are_bubbles :=
    layout.plugRaw_atom_binders_are_bubbles hadmissible
  atom_binders_enclose := layout.plugRaw_atom_binders_enclose hadmissible
  named_references_resolve :=
    plugRaw_named_references_resolve signature input layout
  endpoints_are_valid := layout.plugRaw_endpoints_are_valid hadmissible
  endpoints_are_nodup := layout.plugRaw_endpoints_are_nodup
  wire_endpoints_are_disjoint :=
    plugRaw_wire_endpoints_are_disjoint signature input layout hadmissible
  required_ports_are_covered :=
    plugRaw_required_ports_are_covered signature input layout hadmissible
  wire_scopes_enclose := layout.plugRaw_wire_scopes_enclose hadmissible

end PlugLayout

end VisualProof.Diagram.Splice.Input
