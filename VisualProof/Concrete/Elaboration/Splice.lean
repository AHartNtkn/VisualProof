import VisualProof.Concrete.Elaboration.Compiled
import VisualProof.Concrete.Elaboration.SpliceWireLayout

namespace VisualProof.Concrete.Elaboration

open VisualProof.Diagram
open VisualProof.Theory

private theorem eq_singleton_of_nodup
    {values : List α} {value : α}
    (hnodup : values.Nodup) (hmember : value ∈ values)
    (honly : ∀ other, other ∈ values → other = value) :
    values = [value] := by
  cases values with
  | nil => simp at hmember
  | cons head tail =>
      have hhead : head = value := honly head (by simp)
      subst head
      have htail : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other hother
        have hotherEq : other = value := honly other (by simp [hother])
        subst other
        exact (List.nodup_cons.mp hnodup).1 hother
      subst tail
      rfl

theorem terminal_hiddenWires_eq_nil
    (input : Splice.Input) (terminal : input.TerminalBody)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    input.pattern.val.hiddenWires = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hhidden
  have hidden := (OpenDiagram.mem_hiddenWires input.pattern.val wire).mp hhidden
  have hnotBoundary : wire ∉ input.pattern.val.boundary := by
    intro hboundary
    exact hidden.2 ((OpenDiagram.mem_exposedWires input.pattern.val wire).mpr
      hboundary)
  exact terminal.root_has_no_nonboundary_wires hnonempty wire
    hnotBoundary hidden.1

theorem terminal_nonterminal_exactScopeWires_eq_nil
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    exactScopeWires input.pattern.val.diagram
      (input.binderSpine.proxy proxy) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hwire
  have hscope := (mem_exactScopeWires input.pattern.val.diagram
    (input.binderSpine.proxy proxy) wire).mp hwire
  by_cases hboundary : wire ∈ input.pattern.val.boundary
  · have hrootScope := terminal.boundary_is_root_scoped wire hboundary
    exact input.binderSpine.proxy_ne_root proxy (hscope.symm.trans hrootScope)
  · exact terminal.nonterminal_has_no_nonboundary_wires proxy
      hnonterminal wire hboundary hscope

theorem terminal_root_localOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    localOccurrences input.pattern.val.diagram input.pattern.val.diagram.root =
      [.child (input.binderSpine.proxy
        ⟨0, Nat.pos_of_ne_zero hnonempty⟩)] := by
  let first : Fin input.binderSpine.proxyCount :=
    ⟨0, Nat.pos_of_ne_zero hnonempty⟩
  apply eq_singleton_of_nodup
    (localOccurrences_nodup input.pattern.val.diagram
      input.pattern.val.diagram.root)
  · apply (mem_localOccurrences_child input.pattern.val.diagram
      input.pattern.val.diagram.root
      (input.binderSpine.proxy first)).mpr
    rw [input.binderSpine.proxy_region first]
    rfl
  · intro occurrence hoccurrence
    cases occurrence with
    | node node =>
        have hregion := (mem_localOccurrences_node input.pattern.val.diagram
          input.pattern.val.diagram.root node).mp hoccurrence
        exact False.elim
          (terminal.root_has_no_nodes hnonempty node hregion)
    | child child =>
        have hparent := (mem_localOccurrences_child input.pattern.val.diagram
          input.pattern.val.diagram.root child).mp hoccurrence
        exact congrArg LocalOccurrence.child
          (terminal.root_direct_child hnonempty child hparent)

theorem terminal_root_localNodeOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    localNodeOccurrences input.pattern.val.diagram
      input.pattern.val.diagram.root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence member
  cases occurrence with
  | node node =>
      exact terminal.root_has_no_nodes hnonempty node
        ((mem_localNodeOccurrences_node input.pattern.val.diagram
          input.pattern.val.diagram.root node).mp member)
  | child child => exact (not_mem_localNodeOccurrences_child _ _ _) member

theorem terminal_root_localChildOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    localChildOccurrences input.pattern.val.diagram
        input.pattern.val.diagram.root =
      [.child (input.binderSpine.proxy
        ⟨0, Nat.pos_of_ne_zero hnonempty⟩)] := by
  have combined := terminal_root_localOccurrences input terminal hnonempty
  rw [localOccurrences,
    terminal_root_localNodeOccurrences input terminal hnonempty] at combined
  simpa using combined

theorem terminal_nonterminal_localOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    localOccurrences input.pattern.val.diagram
        (input.binderSpine.proxy proxy) =
      [.child (input.binderSpine.proxy
        ⟨proxy.val + 1, hnonterminal⟩)] := by
  let next : Fin input.binderSpine.proxyCount :=
    ⟨proxy.val + 1, hnonterminal⟩
  apply eq_singleton_of_nodup
    (localOccurrences_nodup input.pattern.val.diagram
      (input.binderSpine.proxy proxy))
  · apply (mem_localOccurrences_child input.pattern.val.diagram
      (input.binderSpine.proxy proxy)
      (input.binderSpine.proxy next)).mpr
    rw [input.binderSpine.proxy_region next]
    rfl
  · intro occurrence hoccurrence
    cases occurrence with
    | node node =>
        have hregion := (mem_localOccurrences_node input.pattern.val.diagram
          (input.binderSpine.proxy proxy) node).mp hoccurrence
        exact False.elim
          (terminal.nonterminal_has_no_nodes proxy hnonterminal node hregion)
    | child child =>
        have hparent := (mem_localOccurrences_child input.pattern.val.diagram
          (input.binderSpine.proxy proxy) child).mp hoccurrence
        exact congrArg LocalOccurrence.child
          (terminal.nonterminal_direct_child proxy hnonterminal child hparent)

theorem terminal_nonterminal_localNodeOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    localNodeOccurrences input.pattern.val.diagram
      (input.binderSpine.proxy proxy) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence member
  cases occurrence with
  | node node =>
      exact terminal.nonterminal_has_no_nodes proxy hnonterminal node
        ((mem_localNodeOccurrences_node input.pattern.val.diagram
          (input.binderSpine.proxy proxy) node).mp member)
  | child child => exact (not_mem_localNodeOccurrences_child _ _ _) member

theorem terminal_nonterminal_localChildOccurrences
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (hnonterminal : proxy.val + 1 < input.binderSpine.proxyCount) :
    localChildOccurrences input.pattern.val.diagram
        (input.binderSpine.proxy proxy) =
      [.child (input.binderSpine.proxy
        ⟨proxy.val + 1, hnonterminal⟩)] := by
  have combined := terminal_nonterminal_localOccurrences input terminal proxy
    hnonterminal
  rw [localOccurrences,
    terminal_nonterminal_localNodeOccurrences input terminal proxy
      hnonterminal] at combined
  simpa using combined

private def terminalRelationBinders (input : Splice.Input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  let patternState := State.ofOpen input.pattern
  let enumeration := CompiledSite.endpoint_binder_enumeration patternState
    input.binderSpine.bodyContainer
  (VisualProof.Data.Finite.allFin
    (CompiledSite.endpointCall patternState
      input.binderSpine.bodyContainer).rels.length).map enumeration.binder

private def terminalProxies (input : Splice.Input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  (VisualProof.Data.Finite.allFin input.binderSpine.proxyCount).map
    input.binderSpine.proxy

private theorem terminalRelationBinders_nodup (input : Splice.Input) :
    (terminalRelationBinders input).Nodup := by
  apply (VisualProof.Data.Finite.allFin_nodup _).map
  intro left right hne heq
  exact hne ((CompiledSite.endpoint_binder_enumeration
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer).binder_injective
      heq)

private theorem terminalProxies_nodup (input : Splice.Input) :
    (terminalProxies input).Nodup := by
  apply (VisualProof.Data.Finite.allFin_nodup _).map
  intro left right hne heq
  exact hne (input.binderSpine.proxy_injective heq)

private theorem terminalBinder_mem_iff_proxy_mem
    (input : Splice.Input)
    (binder : Fin input.pattern.val.diagram.regionCount) :
    binder ∈ terminalProxies input ↔
      binder ∈ terminalRelationBinders input := by
  let patternState := State.ofOpen input.pattern
  let call := CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer
  let enumeration := CompiledSite.endpoint_binder_enumeration patternState
    input.binderSpine.bodyContainer
  constructor
  · intro hproxy
    obtain ⟨proxy, _, hproxy⟩ := List.mem_map.mp hproxy
    let parent := if _hzero : proxy.val = 0 then
      input.pattern.val.diagram.root
    else input.binderSpine.proxy ⟨proxy.val - 1, by omega⟩
    have hregion := input.binderSpine.proxy_region proxy
    change input.pattern.val.diagram.regions (input.binderSpine.proxy proxy) =
      .bubble parent (input.binderSpine.arity proxy) at hregion
    obtain ⟨relation, hlookup⟩ :=
      CompiledSite.endpoint_binders_covers patternState
        input.binderSpine.bodyContainer
        (input.binderSpine.proxy proxy) parent
        (input.binderSpine.arity proxy) hregion
        (input.binderSpine.proxy_encloses_bodyContainer proxy)
    apply List.mem_map.mpr
    refine ⟨relation.index,
      VisualProof.Data.Finite.mem_allFin relation.index, ?_⟩
    exact (enumeration.lookup_owner relation hlookup).trans hproxy
  · intro hrelation
    obtain ⟨relation, _, hrelation⟩ := List.mem_map.mp hrelation
    obtain ⟨parent, hbubble⟩ := enumeration.bubble relation
    obtain ⟨proxy, hproxy⟩ :=
      input.binderSpine.enclosing_bubble_eq_proxy
        input.pattern.property.diagram_well_formed hbubble
        (enumeration.encloses relation)
    apply List.mem_map.mpr
    refine ⟨proxy, VisualProof.Data.Finite.mem_allFin proxy, ?_⟩
    exact hproxy.symm.trans hrelation

private def terminalRelationProxyIndexEquiv (input : Splice.Input) :
    FiniteEquiv (Fin (terminalRelationBinders input).length)
      (Fin (terminalProxies input).length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.regionCount))
    (terminalRelationBinders input) (terminalProxies input)
    (terminalRelationBinders_nodup input) (terminalProxies_nodup input)
    (by
      intro binder
      simpa only [FiniteEquiv.refl_apply] using
        terminalBinder_mem_iff_proxy_mem input binder)

private theorem terminalRelationBinders_length (input : Splice.Input) :
    (terminalRelationBinders input).length =
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels.length := by
  simp [terminalRelationBinders,
    VisualProof.Data.Finite.allFin_eq_finRange]

private theorem terminalProxies_length (input : Splice.Input) :
    (terminalProxies input).length = input.binderSpine.proxyCount := by
  simp [terminalProxies, VisualProof.Data.Finite.allFin_eq_finRange]

noncomputable def terminalRelationProxyEquiv (input : Splice.Input) :
    FiniteEquiv
      (Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels.length)
      (Fin input.binderSpine.proxyCount) :=
  (FiniteEquiv.finCast (terminalRelationBinders_length input).symm).trans
    ((terminalRelationProxyIndexEquiv input).trans
      (FiniteEquiv.finCast (terminalProxies_length input)))

theorem terminalRelationProxyEquiv_binder (input : Splice.Input)
    (relation : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).rels.length) :
    input.binderSpine.proxy (terminalRelationProxyEquiv input relation) =
      (CompiledSite.endpoint_binder_enumeration (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).binder relation := by
  have hspec := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.pattern.val.diagram.regionCount))
    (terminalRelationBinders input) (terminalProxies input)
    (terminalRelationBinders_nodup input) (terminalProxies_nodup input)
    (by
      intro binder
      simpa only [FiniteEquiv.refl_apply] using
        terminalBinder_mem_iff_proxy_mem input binder)
    (FiniteEquiv.finCast (terminalRelationBinders_length input).symm relation)
  simpa [terminalRelationProxyEquiv, terminalRelationProxyIndexEquiv,
    terminalRelationBinders, terminalProxies, FiniteEquiv.finCast,
    VisualProof.Data.Finite.allFin_eq_finRange] using hspec

theorem terminalRelationProxyEquiv_arity (input : Splice.Input)
    (relation : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).rels.length) :
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels.get relation =
      input.binderSpine.arity (terminalRelationProxyEquiv input relation) := by
  let enumeration := CompiledSite.endpoint_binder_enumeration
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer
  obtain ⟨parent, hbubble⟩ := enumeration.bubble relation
  have hproxy := input.binderSpine.proxy_region
    (terminalRelationProxyEquiv input relation)
  rw [terminalRelationProxyEquiv_binder input relation] at hproxy
  exact (CRegion.bubble.inj (hbubble.symm.trans hproxy)).2

theorem terminalRelationProxyEquiv_lookup (input : Splice.Input)
    (relation : RelVar
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels arity) :
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).binders
        (input.binderSpine.proxy
          (terminalRelationProxyEquiv input relation.index)) =
      some ⟨arity, relation⟩ := by
  cases relation with
  | mk index hasArity =>
      cases hasArity
      rw [terminalRelationProxyEquiv_binder input index]
      simpa using (CompiledSite.endpoint_binder_enumeration
        (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).lookup index

private theorem terminalProxy_focus_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    (outer : WireContext input.pattern.val.diagram)
    (rels : RelCtx)
    (binders : BinderContext input.pattern.val.diagram rels)
    (body : CompiledRegion input.pattern.val.diagram
      (.nested (input.binderSpine.proxy proxy) outer rels binders))
    (compiled : compileRegion? input.pattern.val.diagram
      input.pattern.property.diagram_well_formed
      (input.binderSpine.proxy proxy) outer binders = some body)
    (outerEq : outer = input.pattern.val.exposedWires)
    {focus : CompiledFocus body}
    (found : body.focus? input.binderSpine.bodyContainer = some focus) :
    focus.endpointCall.outerContext = input.pattern.val.exposedWires := by
  by_cases hterminal : proxy.val + 1 = input.binderSpine.proxyCount
  · have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
      have := proxy.isLt
      omega
    have hbody : input.binderSpine.bodyContainer =
        input.binderSpine.proxy proxy := by
      rw [input.binderSpine.body_eq_terminal_of_nonempty hnonzero]
      apply congrArg input.binderSpine.proxy
      apply Fin.ext
      simp
      omega
    rw [hbody] at found
    have originFound := CompiledRegion.focus?_origin body
    have focusEq := Option.some.inj (originFound.symm.trans found)
    subst focus
    exact outerEq
  · have hnonterminal :
        proxy.val + 1 < input.binderSpine.proxyCount := by omega
    let next : Fin input.binderSpine.proxyCount :=
      ⟨proxy.val + 1, hnonterminal⟩
    have nextRegion : input.pattern.val.diagram.regions
        (input.binderSpine.proxy next) =
      .bubble (input.binderSpine.proxy proxy)
        (input.binderSpine.arity next) := by
      rw [input.binderSpine.proxy_region next]
      simp only [next]
      split
      next hzero => omega
      next _ =>
        congr 1
    obtain ⟨nextBody, nextCompiled, bodyEq⟩ :=
      CompilerCall.compile?_singleton_bubble
        input.pattern.property.diagram_well_formed
        (.nested (input.binderSpine.proxy proxy) outer rels binders)
        (input.binderSpine.proxy next) (input.binderSpine.arity next)
        (terminal_nonterminal_localNodeOccurrences input terminal proxy
          hnonterminal)
        (terminal_nonterminal_localChildOccurrences input terminal proxy
          hnonterminal)
        nextRegion compiled
    subst body
    have different : input.binderSpine.proxy proxy ≠
        input.binderSpine.bodyContainer := by
      intro heq
      have hnonzero : input.binderSpine.proxyCount ≠ 0 := by
        have := proxy.isLt
        omega
      rw [input.binderSpine.body_eq_terminal_of_nonempty hnonzero] at heq
      have hindex := input.binderSpine.proxy_injective heq
      have := congrArg Fin.val hindex
      simp at this
      omega
    cases nextFound : nextBody.focus? input.binderSpine.bodyContainer with
    | none =>
        have parentFound := CompiledRegion.focus?_singleton_bubble_eq
          (body := nextBody) input.binderSpine.bodyContainer different
        rw [parentFound, nextFound] at found
        contradiction
    | some nextFocus =>
        have expected := CompiledRegion.focus?_singleton_bubble
          (body := nextBody) different nextFound
        have focusEq := Option.some.inj (expected.symm.trans found)
        subst focus
        have nextOuterEq :
            ((CompilerCall.nested (input.binderSpine.proxy proxy) outer rels
              binders).fullContext) = input.pattern.val.exposedWires := by
          simp [CompilerCall.fullContext, CompilerCall.localContext,
            CompilerCall.outerContext,
            terminal_nonterminal_exactScopeWires_eq_nil input terminal proxy
              hnonterminal, outerEq]
        exact terminalProxy_focus_outerContext input terminal next
          ((CompilerCall.nested (input.binderSpine.proxy proxy) outer rels
            binders).fullContext)
          (input.binderSpine.arity next :: rels)
          (binders.push (input.binderSpine.proxy next)
            (input.binderSpine.arity next))
          nextBody nextCompiled nextOuterEq nextFound
termination_by input.binderSpine.proxyCount - proxy.val

theorem patternTerminal_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody) :
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).outerContext =
        input.pattern.val.exposedWires := by
  let patternState := State.ofOpen input.pattern
  by_cases hzero : input.binderSpine.proxyCount = 0
  · have hbody := input.binderSpine.body_eq_root_of_empty hzero
    change (CompiledSite.focus patternState
      input.binderSpine.bodyContainer).endpointCall.outerContext = _
    rw [hbody]
    simpa [patternState] using congrArg
      (fun focus => focus.endpointCall.outerContext)
      (CompiledSite.focus_root (State.ofOpen input.pattern))
  · let first : Fin input.binderSpine.proxyCount :=
      ⟨0, Nat.pos_of_ne_zero hzero⟩
    have firstRegion : input.pattern.val.diagram.regions
        (input.binderSpine.proxy first) =
      .bubble input.pattern.val.diagram.root
        (input.binderSpine.arity first) := by
      rw [input.binderSpine.proxy_region first]
      simp [first]
    have hiddenEq := terminal_hiddenWires_eq_nil input terminal hzero
    have firstOuterEq :
        ((CompilerCall.root input.pattern.val.exposedWires
          input.pattern.val.hiddenWires).fullContext) =
            input.pattern.val.exposedWires := by
      simp [CompilerCall.fullContext, CompilerCall.outerContext,
        CompilerCall.localContext, hiddenEq]
    have rootCase :
        ∀ (rootBody : CompiledRegion input.pattern.val.diagram
            (.root input.pattern.val.exposedWires
              input.pattern.val.hiddenWires))
          (rootCompiled :
            (CompilerCall.root input.pattern.val.exposedWires
              input.pattern.val.hiddenWires).compile?
                input.pattern.val.diagram
                input.pattern.property.diagram_well_formed = some rootBody)
          {rootFocus : CompiledFocus rootBody},
          rootBody.focus? input.binderSpine.bodyContainer = some rootFocus →
            rootFocus.endpointCall.outerContext =
              input.pattern.val.exposedWires := by
      intro rootBody rootCompiled rootFocus rootFound
      obtain ⟨firstBody, firstCompiled, rootBodyEq⟩ :=
        CompilerCall.compile?_singleton_bubble
          input.pattern.property.diagram_well_formed
          (.root input.pattern.val.exposedWires input.pattern.val.hiddenWires)
          (input.binderSpine.proxy first) (input.binderSpine.arity first)
          (terminal_root_localNodeOccurrences input terminal hzero)
          (terminal_root_localChildOccurrences input terminal hzero)
          firstRegion rootCompiled
      subst rootBody
      have rootDifferent : input.pattern.val.diagram.root ≠
          input.binderSpine.bodyContainer := by
        intro heq
        rw [input.binderSpine.body_eq_terminal_of_nonempty hzero] at heq
        exact input.binderSpine.proxy_ne_root _ heq.symm
      cases firstFound : firstBody.focus? input.binderSpine.bodyContainer with
      | none =>
          have parentFound := CompiledRegion.focus?_singleton_bubble_eq
            (body := firstBody) input.binderSpine.bodyContainer rootDifferent
          rw [parentFound, firstFound] at rootFound
          contradiction
      | some firstFocus =>
          have expected := CompiledRegion.focus?_singleton_bubble
            (body := firstBody) rootDifferent firstFound
          have focusEq := Option.some.inj (expected.symm.trans rootFound)
          rw [← focusEq]
          exact terminalProxy_focus_outerContext input terminal first
            ((CompilerCall.root input.pattern.val.exposedWires
              input.pattern.val.hiddenWires).fullContext)
            [input.binderSpine.arity first]
            (BinderContext.empty.push (input.binderSpine.proxy first)
              (input.binderSpine.arity first))
            firstBody firstCompiled firstOuterEq firstFound
    let result := CompiledSite.focus patternState
      input.binderSpine.bodyContainer
    have found : input.pattern.compilation.focus?
        input.binderSpine.bodyContainer = some result :=
      (Option.some_get (CheckedOpen.compilation_focus?_isSome input.pattern
        input.binderSpine.bodyContainer)).symm
    change result.endpointCall.outerContext = _
    exact rootCase input.pattern.compilation
      input.pattern.compilation_computation found

namespace CompiledSite

private theorem castWire_scope
    {source target : Diagram} (equality : source = target)
    (wire : Fin source.wireCount) :
    (target.wires (Fin.cast (congrArg Diagram.wireCount equality) wire)).scope =
      Fin.cast (congrArg Diagram.regionCount equality)
        (source.wires wire).scope := by
  cases equality
  rfl

private theorem encloses_cast
    {source target : Diagram} (equality : source = target)
    {ancestor descendant : Fin source.regionCount}
    (encloses : source.Encloses ancestor descendant) :
    target.Encloses
      (Fin.cast (congrArg Diagram.regionCount equality) ancestor)
      (Fin.cast (congrArg Diagram.regionCount equality) descendant) := by
  cases equality
  exact encloses

private def sourceSite {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram) :
    Fin source.checked.val.diagram.regionCount :=
  Fin.cast (congrArg (fun frame : Checked => frame.val.regionCount) frameEq)
    input.site

private def sourceWire {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (wire : Fin input.frame.val.wireCount) :
    Fin source.checked.val.diagram.wireCount :=
  Fin.cast (congrArg (fun frame : Checked => frame.val.wireCount) frameEq) wire

private def sourceRegion {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (region : Fin input.frame.val.regionCount) :
    Fin source.checked.val.diagram.regionCount :=
  Fin.cast (congrArg (fun frame : Checked => frame.val.regionCount) frameEq)
    region

private theorem spliceAttachment_mem
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (layout : input.PlugLayout)
    (external : Fin input.pattern.val.exposedWires.length) :
    sourceWire input frameEq
        (input.attachment (layout.exposedPosition external)) ∈
      (endpointCall source (sourceSite input frameEq)).fullContext := by
  apply ((endpoint_fullContext_exact source
    (sourceSite input frameEq)).mem_iff _).mpr
  let diagramEq : input.frame.val = source.checked.val.diagram :=
    congrArg (fun frame : Checked => frame.val) frameEq
  have visible := admissible.attachments_visible
    (layout.exposedPosition external)
  have castVisible := encloses_cast diagramEq visible
  rw [← castWire_scope diagramEq] at castVisible
  simpa [sourceSite, sourceWire, diagramEq] using castVisible

noncomputable def spliceAttachmentPosition
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (layout : input.PlugLayout)
    (external : Fin input.pattern.val.exposedWires.length) :
    Fin (endpointCall source (sourceSite input frameEq)).fullContext.length :=
  ((endpointCall source (sourceSite input frameEq)).fullContext.lookup?
    (sourceWire input frameEq
      (input.attachment (layout.exposedPosition external)))).get
        (Option.isSome_iff_exists.mpr
          (WireContext.lookup?_complete
            (spliceAttachment_mem input frameEq admissible layout external)))

theorem spliceAttachmentPosition_get
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (layout : input.PlugLayout)
    (external : Fin input.pattern.val.exposedWires.length) :
    (endpointCall source (sourceSite input frameEq)).fullContext.get
        (spliceAttachmentPosition input frameEq admissible layout external) =
      sourceWire input frameEq
        (input.attachment (layout.exposedPosition external)) := by
  apply WireContext.lookup?_sound
  exact (Option.some_get (Option.isSome_iff_exists.mpr
    (WireContext.lookup?_complete
      (spliceAttachment_mem input frameEq admissible layout external)))).symm

noncomputable def spliceWireMap
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (layout : input.PlugLayout) :
    Fin (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).outerContext.length →
      Fin (endpointCall source (sourceSite input frameEq)).fullContext.length :=
  fun wire => spliceAttachmentPosition input frameEq admissible layout
    (Fin.cast (congrArg List.length
      (patternTerminal_outerContext input admissible.terminal_body)) wire)

theorem spliceWireMap_get
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (layout : input.PlugLayout)
    (wire : Fin (endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).outerContext.length) :
    (endpointCall source (sourceSite input frameEq)).fullContext.get
        (spliceWireMap input frameEq admissible layout wire) =
      sourceWire input frameEq (input.attachment
        (layout.exposedPosition (Fin.cast (congrArg List.length
          (patternTerminal_outerContext input admissible.terminal_body))
            wire))) :=
  spliceAttachmentPosition_get input frameEq admissible layout _

private theorem castBubble
    {source target : Diagram} (equality : source = target)
    {binder parent : Fin source.regionCount} {arity : Nat}
    (bubble : source.regions binder = .bubble parent arity) :
    target.regions
        (Fin.cast (congrArg Diagram.regionCount equality) binder) =
      .bubble (Fin.cast (congrArg Diagram.regionCount equality) parent) arity := by
  cases equality
  exact bubble

private theorem spliceRelation_exists
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (relation : RelVar
      (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels relationArity) :
    ∃ targetRelation : RelVar
        (endpointCall source (sourceSite input frameEq)).rels relationArity,
      (endpointCall source (sourceSite input frameEq)).binders
          (sourceRegion input frameEq (input.binderTarget
            (terminalRelationProxyEquiv input relation.index))) =
        some ⟨relationArity, targetRelation⟩ := by
  let proxy := terminalRelationProxyEquiv input relation.index
  have proxyArity : input.binderSpine.arity proxy = relationArity :=
    (terminalRelationProxyEquiv_arity input relation.index).symm.trans
      relation.hasArity
  obtain ⟨parent, bubble⟩ := admissible.binder_targets_match proxy
  rw [proxyArity] at bubble
  let diagramEq : input.frame.val = source.checked.val.diagram :=
    congrArg (fun frame : Checked => frame.val) frameEq
  have castedBubble := castBubble diagramEq bubble
  have castedEncloses := encloses_cast diagramEq
    (admissible.binder_targets_enclose proxy)
  simpa [sourceRegion, sourceSite, diagramEq] using
    (endpoint_binders_covers source (sourceSite input frameEq)
      (sourceRegion input frameEq (input.binderTarget proxy))
      (Fin.cast (congrArg Diagram.regionCount diagramEq) parent)
      relationArity castedBubble castedEncloses)

noncomputable def spliceRelationMap
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible) :
    RelationRenaming
      (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels
      (endpointCall source (sourceSite input frameEq)).rels :=
  fun relation => Classical.choose
    (spliceRelation_exists input frameEq admissible relation)

theorem spliceRelationMap_lookup
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (relation : RelVar
      (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels relationArity) :
    (endpointCall source (sourceSite input frameEq)).binders
        (sourceRegion input frameEq (input.binderTarget
          (terminalRelationProxyEquiv input relation.index))) =
      some ⟨relationArity,
        spliceRelationMap input frameEq admissible relation⟩ :=
  Classical.choose_spec (spliceRelation_exists input frameEq admissible relation)

noncomputable def spliceAfter
    {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (admissible : input.Admissible)
    (layout : input.PlugLayout) :
    Region (endpointCall source (sourceSite input frameEq)).outerContext.length
      (endpointCall source (sourceSite input frameEq)).rels :=
  Region.spliceAt
    (endpointCall source (sourceSite input frameEq)).localContext.length
    ((endpointCall source (sourceSite input frameEq)).castFullItems
      (directItems source (sourceSite input frameEq)).erase)
    (body (State.ofOpen input.pattern) input.binderSpine.bodyContainer)
    (fun wire => Fin.cast
      (endpointCall source (sourceSite input frameEq)).fullContext_length
        (spliceWireMap input frameEq admissible layout wire))
    (spliceRelationMap input frameEq admissible)

end CompiledSite

end VisualProof.Concrete.Elaboration
