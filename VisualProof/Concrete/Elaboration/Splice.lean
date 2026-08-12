import VisualProof.Concrete.Elaboration.Compiled
import VisualProof.Concrete.Elaboration.SpliceWireLayout
import VisualProof.Concrete.Subgraph.Splice.Input.Quotient

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

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

private theorem compiledCall_eq_singletonBubble
    {d : Diagram} (hwf : d.WellFormed)
    {call : CompilerCall d} {region : CompiledRegion d call}
    {child : Fin d.regionCount} {arity : Nat}
    (compiled : call.compile? d hwf = some region)
    (occurrences : localOccurrences d call.origin = [.child child])
    (shape : d.regions child = .bubble call.origin arity) :
    ∃ body : CompiledRegion d (.nested child call.fullContext
        (arity :: call.rels) (call.binders.push child arity)),
      region = .mk (.cons (.bubble arity body) .nil) ∧
      compileRegion? d hwf child call.fullContext
        (call.binders.push child arity) = some body := by
  cases region with
  | mk sourceItems =>
      have itemsCompiled := call.compile?_items_of_success hwf compiled
      have direct : LocalOccurrence.child child ∈
          localOccurrences d call.origin := by
        rw [occurrences]
        simp
      let singletonDirect : ∀ occurrence,
          occurrence ∈ [.child child] →
            occurrence ∈ localOccurrences d call.origin := by
        intro occurrence member
        have occurrenceEq : occurrence = .child child := by simpa using member
        subst occurrence
        exact direct
      have itemsSingleton : compileItems? d hwf call.origin call.fullContext
          call.binders [.child child] singletonDirect = some sourceItems :=
        (compileItems?_congr_occurrences hwf call.origin call.fullContext
          call.binders occurrences (fun _ member => member)
          singletonDirect).symm.trans itemsCompiled
      rw [compileItems?_cons] at itemsSingleton
      rw [compileOccurrence?_child_bubble hwf call.origin child
        call.fullContext call.binders arity direct shape] at itemsSingleton
      cases bodyCompiled : compileRegion? d hwf child call.fullContext
          (call.binders.push child arity) with
      | none => simp [bodyCompiled] at itemsSingleton
      | some body =>
          simp [bodyCompiled] at itemsSingleton
          have regionEq :
              (CompiledRegion.mk sourceItems : CompiledRegion d call) =
                .mk (.cons (.bubble arity body) .nil) := by
            cases call <;> cases itemsSingleton <;> rfl
          exact ⟨body, regionEq, rfl⟩

private theorem focus_singletonBubble_elim
    {d : Diagram} {call : CompilerCall d}
    {region : CompiledRegion d call}
    {origin : Fin d.regionCount} {arity : Nat}
    {body : CompiledRegion d (.nested origin call.fullContext
      (arity :: call.rels) (call.binders.push origin arity))}
    {site : Fin d.regionCount} {focus : CompiledFocus region site}
    {claim : CompilerCall d → Prop}
    (regionEq : region = .mk (.cons (.bubble arity body) .nil))
    (different : call.origin ≠ site)
    (found : region.focus? site = some focus)
    (child : ∀ childFocus, body.focus? site = some childFocus →
      claim childFocus.endpointCall) :
    claim focus.endpointCall := by
  cases regionEq
  rw [CompiledRegion.focus?_singleton_bubble different] at found
  cases childFound : body.focus? site with
  | none => simp [childFound] at found
  | some childFocus =>
      simp only [childFound, Option.map_some, Option.some.injEq] at found
      cases found
      exact child childFocus childFound

private theorem terminalProxy_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody)
    (proxy : Fin input.binderSpine.proxyCount)
    {call : CompilerCall input.pattern.val.diagram}
    {region : CompiledRegion input.pattern.val.diagram call}
    (originEq : call.origin = input.binderSpine.proxy proxy)
    (compiled : call.compile? input.pattern.val.diagram
      input.pattern.property.diagram_well_formed = some region)
    (outerEq : call.outerContext = input.pattern.val.exposedWires)
    {focus : CompiledFocus region input.binderSpine.bodyContainer}
    (found : region.focus? input.binderSpine.bodyContainer = some focus) :
    focus.endpointCall.outerContext = input.pattern.val.exposedWires := by
  by_cases terminalProxy : proxy.val + 1 = input.binderSpine.proxyCount
  · have nonempty : input.binderSpine.proxyCount ≠ 0 := by
      have := proxy.isLt
      omega
    have bodyEq : input.binderSpine.bodyContainer =
        input.binderSpine.proxy proxy := by
      rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty]
      apply congrArg input.binderSpine.proxy
      apply Fin.ext
      simp
      omega
    have endpointEq : call.origin = input.binderSpine.bodyContainer :=
      originEq.trans bodyEq.symm
    exact (CompiledRegion.focus?_same_outerContext endpointEq found).trans outerEq
  · have nonterminal : proxy.val + 1 < input.binderSpine.proxyCount := by
      omega
    let next : Fin input.binderSpine.proxyCount :=
      ⟨proxy.val + 1, nonterminal⟩
    have nextShape : input.pattern.val.diagram.regions
        (input.binderSpine.proxy next) =
      .bubble (input.binderSpine.proxy proxy)
        (input.binderSpine.arity next) := by
      rw [input.binderSpine.proxy_region next]
      simp [next]
    have occurrences : localOccurrences input.pattern.val.diagram call.origin =
        [.child (input.binderSpine.proxy next)] := by
      rw [originEq]
      exact terminal_nonterminal_localOccurrences input terminal proxy nonterminal
    obtain ⟨body, regionEq, bodyCompiled⟩ :=
      compiledCall_eq_singletonBubble input.pattern.property.diagram_well_formed
        compiled occurrences (by simpa [originEq] using nextShape)
    subst region
    have different : call.origin ≠ input.binderSpine.bodyContainer := by
      intro equality
      have nonempty : input.binderSpine.proxyCount ≠ 0 := by
        have := proxy.isLt
        omega
      rw [input.binderSpine.body_eq_terminal_of_nonempty nonempty] at equality
      have indices := input.binderSpine.proxy_injective
        (originEq.symm.trans equality)
      have values := congrArg Fin.val indices
      simp at values
      omega
    rw [CompiledRegion.focus?_singleton_bubble different] at found
    cases nextFound : body.focus? input.binderSpine.bodyContainer with
    | none => simp [nextFound] at found
    | some nextFocus =>
        simp only [nextFound, Option.map_some, Option.some.injEq] at found
        cases found
        apply terminalProxy_outerContext input terminal next rfl bodyCompiled
        · have localEq : call.localContext = [] := by
            cases call with
            | root ambient locals =>
                exact False.elim
                  (input.binderSpine.proxy_ne_root proxy originEq.symm)
            | nested origin context rels binders =>
                change exactScopeWires input.pattern.val.diagram origin = []
                change origin = input.binderSpine.proxy proxy at originEq
                rw [originEq]
                exact terminal_nonterminal_exactScopeWires_eq_nil input
                  terminal proxy nonterminal
          rw [CompilerCall.fullContext, localEq, outerEq, List.append_nil]
          rfl
        · exact nextFound
termination_by input.binderSpine.proxyCount - proxy.val

theorem patternTerminal_outerContext
    (input : Splice.Input) (terminal : input.TerminalBody) :
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).outerContext =
        input.pattern.val.exposedWires := by
  let patternState := State.ofOpen input.pattern
  let focus := CompiledSite.focus patternState input.binderSpine.bodyContainer
  have found : input.pattern.compilation.focus?
      input.binderSpine.bodyContainer = some focus := by
    exact CompiledSite.focus_computation patternState
      input.binderSpine.bodyContainer
  change focus.endpointCall.outerContext = input.pattern.val.exposedWires
  by_cases empty : input.binderSpine.proxyCount = 0
  · have bodyEq := input.binderSpine.body_eq_root_of_empty empty
    exact CompiledRegion.focus?_same_outerContext bodyEq.symm found
  · let first : Fin input.binderSpine.proxyCount :=
      ⟨0, Nat.pos_of_ne_zero empty⟩
    have firstShape : input.pattern.val.diagram.regions
        (input.binderSpine.proxy first) =
      .bubble input.pattern.val.diagram.root
        (input.binderSpine.arity first) := by
      rw [input.binderSpine.proxy_region first]
      simp [first]
    have occurrences := terminal_root_localOccurrences input terminal empty
    obtain ⟨body, regionEq, bodyCompiled⟩ :=
      compiledCall_eq_singletonBubble input.pattern.property.diagram_well_formed
        input.pattern.compilation_computation occurrences firstShape
    have different : input.pattern.val.diagram.root ≠
        input.binderSpine.bodyContainer := by
      intro equality
      rw [input.binderSpine.body_eq_terminal_of_nonempty empty] at equality
      exact input.binderSpine.proxy_ne_root _ equality.symm
    apply focus_singletonBubble_elim
      (claim := fun call => call.outerContext = input.pattern.val.exposedWires)
      regionEq different found
    intro firstFocus firstFound
    apply terminalProxy_outerContext input terminal first rfl bodyCompiled
    · change (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires) = input.pattern.val.exposedWires
      rw [terminal_hiddenWires_eq_nil input terminal empty,
        List.append_nil]
    · exact firstFound

private noncomputable def terminalRelationBinders (input : Splice.Input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  let patternState := State.ofOpen input.pattern
  let enumeration := CompiledSite.endpoint_binders_enumeration patternState
    input.binderSpine.bodyContainer
  (allFin (CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer).rels.length).map enumeration.binder

private def terminalProxies (input : Splice.Input) :
    List (Fin input.pattern.val.diagram.regionCount) :=
  (allFin input.binderSpine.proxyCount).map input.binderSpine.proxy

private theorem terminalRelationBinders_nodup (input : Splice.Input) :
    (terminalRelationBinders input).Nodup := by
  apply (allFin_nodup _).map
  intro left right different equal
  exact different ((CompiledSite.endpoint_binders_enumeration
    (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer).binder_injective equal)

private theorem terminalProxies_nodup (input : Splice.Input) :
    (terminalProxies input).Nodup := by
  apply (allFin_nodup _).map
  intro left right different equal
  exact different (input.binderSpine.proxy_injective equal)

private theorem terminalBinder_mem_iff_proxy_mem
    (input : Splice.Input)
    (binder : Fin input.pattern.val.diagram.regionCount) :
    binder ∈ terminalProxies input ↔
      binder ∈ terminalRelationBinders input := by
  let patternState := State.ofOpen input.pattern
  let call := CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer
  let enumeration := CompiledSite.endpoint_binders_enumeration patternState
    input.binderSpine.bodyContainer
  constructor
  · intro proxyMember
    obtain ⟨proxy, _, proxyEq⟩ := List.mem_map.mp proxyMember
    let parent := if _zero : proxy.val = 0 then
      input.pattern.val.diagram.root
    else input.binderSpine.proxy ⟨proxy.val - 1, by omega⟩
    have shape := input.binderSpine.proxy_region proxy
    change input.pattern.val.diagram.regions (input.binderSpine.proxy proxy) =
      .bubble parent (input.binderSpine.arity proxy) at shape
    obtain ⟨relation, lookup⟩ :=
      CompiledSite.endpoint_binders_covers patternState
        input.binderSpine.bodyContainer
        (input.binderSpine.proxy proxy) parent
        (input.binderSpine.arity proxy) shape
        (input.binderSpine.proxy_encloses_bodyContainer proxy)
    apply List.mem_map.mpr
    refine ⟨relation.index, mem_allFin relation.index, ?_⟩
    exact (enumeration.lookup_owner relation lookup).trans proxyEq
  · intro relationMember
    obtain ⟨relation, _, relationEq⟩ := List.mem_map.mp relationMember
    obtain ⟨parent, bubble⟩ := enumeration.bubble relation
    obtain ⟨proxy, proxyEq⟩ :=
      input.binderSpine.enclosing_bubble_eq_proxy
        input.pattern.property.diagram_well_formed bubble
        (enumeration.encloses relation)
    apply List.mem_map.mpr
    exact ⟨proxy, mem_allFin proxy, proxyEq.symm.trans relationEq⟩

private theorem terminalRelationBinders_length (input : Splice.Input) :
    (terminalRelationBinders input).length =
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels.length := by
  simp [terminalRelationBinders, allFin_eq_finRange]

private theorem terminalProxies_length (input : Splice.Input) :
    (terminalProxies input).length = input.binderSpine.proxyCount := by
  simp [terminalProxies, allFin_eq_finRange]

private noncomputable def terminalRelationProxyIndexEquiv
    (input : Splice.Input) :
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
      (CompiledSite.endpoint_binders_enumeration (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).binder relation := by
  have spec := FiniteEquiv.restrictLists_spec
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
    allFin_eq_finRange] using spec

theorem terminalRelationProxyEquiv_arity (input : Splice.Input)
    (relation : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).rels.length) :
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels.get relation =
      input.binderSpine.arity (terminalRelationProxyEquiv input relation) := by
  let enumeration := CompiledSite.endpoint_binders_enumeration
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer
  obtain ⟨parent, bubble⟩ := enumeration.bubble relation
  have proxyShape := input.binderSpine.proxy_region
    (terminalRelationProxyEquiv input relation)
  rw [terminalRelationProxyEquiv_binder input relation] at proxyShape
  exact (CRegion.bubble.inj (bubble.symm.trans proxyShape)).2

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
      simpa using (CompiledSite.endpoint_binders_enumeration
        (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).lookup index

private theorem list_get_cast_of_eq {first second : List α}
    (equality : first = second) (index : Fin first.length) :
    first.get index = second.get
      (Fin.cast (congrArg List.length equality) index) := by
  subst second
  rfl

/-- Every local wire of the canonical terminal compiler call is an internal
wire scoped exactly at the terminal body. -/
theorem patternTerminal_localWire
    (input : Splice.Input)
    (index : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).localContext.length) :
    let wire := (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).localContext.get index
    wire ∉ input.pattern.val.exposedWires ∧
      (input.pattern.val.diagram.wires wire).scope =
        input.binderSpine.bodyContainer := by
  let patternState := State.ofOpen input.pattern
  let call := CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer
  let wire := call.localContext.get index
  change wire ∉ input.pattern.val.exposedWires ∧
    (input.pattern.val.diagram.wires wire).scope =
      input.binderSpine.bodyContainer
  by_cases empty : input.binderSpine.proxyCount = 0
  · have bodyEq := input.binderSpine.body_eq_root_of_empty empty
    have focusEq := CompiledSite.focus_root patternState
    have callEq : call = .root input.pattern.val.exposedWires
        input.pattern.val.hiddenWires := by
      simpa [call, patternState, bodyEq] using
        congrArg CompiledFocus.endpointCall focusEq
    have localEq : call.localContext = input.pattern.val.hiddenWires := by
      rw [callEq]
      rfl
    let index' : Fin input.pattern.val.hiddenWires.length :=
      Fin.cast (congrArg List.length localEq) index
    have wireEq : wire = input.pattern.val.hiddenWires.get index' := by
      exact list_get_cast_of_eq localEq index
    rw [wireEq]
    have hidden := (OpenDiagram.mem_hiddenWires input.pattern.val
      (input.pattern.val.hiddenWires.get index')).mp (List.get_mem _ _)
    exact ⟨hidden.2, hidden.1.trans bodyEq.symm⟩
  · have bodyNeRoot : input.binderSpine.bodyContainer ≠
        input.pattern.val.diagram.root := by
      rw [input.binderSpine.body_eq_terminal_of_nonempty empty]
      exact input.binderSpine.proxy_ne_root _
    cases callEq : call with
    | root ambient locals =>
        have originEq := CompiledSite.endpoint_origin patternState
          input.binderSpine.bodyContainer
        simp [call, callEq, CompilerCall.origin] at originEq
        exact (bodyNeRoot originEq.symm).elim
    | nested origin context rels binders =>
        have originEq : origin = input.binderSpine.bodyContainer := by
          simpa [call, callEq, CompilerCall.origin] using
            CompiledSite.endpoint_origin patternState
              input.binderSpine.bodyContainer
        have localEq : call.localContext =
            exactScopeWires input.pattern.val.diagram origin := by
          rw [callEq]
          rfl
        let index' : Fin (exactScopeWires input.pattern.val.diagram
            origin).length :=
          Fin.cast (congrArg List.length localEq) index
        have wireEq : wire =
            (exactScopeWires input.pattern.val.diagram origin).get index' := by
          exact list_get_cast_of_eq localEq index
        have scopeEq : (input.pattern.val.diagram.wires wire).scope =
            input.binderSpine.bodyContainer := by
          rw [wireEq, (mem_exactScopeWires input.pattern.val.diagram origin
            ((exactScopeWires input.pattern.val.diagram origin).get
              index')).mp (List.get_mem _ _), originEq]
        refine ⟨?_, scopeEq⟩
        intro exposed
        have rootScope := input.pattern.property.exposed_root_scoped exposed
        exact bodyNeRoot (scopeEq.symm.trans rootScope)

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
