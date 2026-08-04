import VisualProof.Diagram.Concrete.Elaboration.Compile.Elaborate

namespace VisualProof.Diagram

open ConcreteElaboration
open VisualProof.Data.Finite
open VisualProof.Theory

private theorem certifiedExactScopeWires_mem_iff
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (region : Fin source.regionCount) (wire : Fin source.wireCount) :
    equiv.wires wire ∈ exactScopeWires target (equiv.regions region) ↔
      wire ∈ exactScopeWires source region := by
  simp only [mem_exactScopeWires]
  rw [← equiv.wire_scope_eq wire]
  constructor
  · intro equality
    have := congrArg equiv.regions.invFun equality
    simpa only [equiv.regions.left_inv] using this
  · exact congrArg equiv.regions

private def certifiedLocalWireEquiv {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (exactScopeWires source region).length)
      (Fin (exactScopeWires target (equiv.regions region)).length) :=
  FiniteEquiv.restrictLists equiv.wires _ _
    (exactScopeWires_nodup source region)
    (exactScopeWires_nodup target (equiv.regions region))
    (certifiedExactScopeWires_mem_iff equiv region)

private theorem certifiedLocalWireEquiv_spec
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (region : Fin source.regionCount)
    (index : Fin (exactScopeWires source region).length) :
    (exactScopeWires target (equiv.regions region)).get
        (certifiedLocalWireEquiv equiv region index) =
      equiv.wires ((exactScopeWires source region).get index) :=
  FiniteEquiv.restrictLists_spec equiv.wires _ _ _ _ _ index

private theorem certifiedLocalOccurrences_mem_iff
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (region : Fin source.regionCount)
    (occurrence : LocalOccurrence source.regionCount source.nodeCount) :
    certifiedRenameOccurrence equiv occurrence ∈
        localOccurrences target (equiv.regions region) ↔
      occurrence ∈ localOccurrences source region := by
  cases occurrence with
  | node node =>
      simp only [certifiedRenameOccurrence, mem_localOccurrences_node]
      rw [← equiv.node_region_eq node]
      constructor
      · intro equality
        have := congrArg equiv.regions.invFun equality
        simpa only [equiv.regions.left_inv] using this
      · exact congrArg equiv.regions
  | child child =>
      simp only [certifiedRenameOccurrence, mem_localOccurrences_child]
      rw [← equiv.regions_eq child, CRegion.parent?_rename]
      cases hparent : (source.regions child).parent? with
      | none => simp
      | some parent =>
          simp only [Option.map_some, Option.some.injEq]
          constructor
          · intro equality
            have := congrArg equiv.regions.invFun equality
            simpa only [equiv.regions.left_inv] using this
          · exact congrArg equiv.regions

private def certifiedLocalOccurrenceEquiv {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (localOccurrences source region).length)
      (Fin (localOccurrences target (equiv.regions region)).length) :=
  FiniteEquiv.restrictLists (certifiedOccurrenceEquiv equiv) _ _
    (localOccurrences_nodup source region)
    (localOccurrences_nodup target (equiv.regions region))
    (certifiedLocalOccurrences_mem_iff equiv region)

private theorem certifiedLocalOccurrenceEquiv_spec
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (region : Fin source.regionCount)
    (index : Fin (localOccurrences source region).length) :
    (localOccurrences target (equiv.regions region)).get
        (certifiedLocalOccurrenceEquiv equiv region index) =
      certifiedRenameOccurrence equiv
        ((localOccurrences source region).get index) :=
  FiniteEquiv.restrictLists_spec (certifiedOccurrenceEquiv equiv) _ _ _ _ _ index

def CertifiedWireContextsAgree {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)) : Prop :=
  ∀ index, targetContext.get (ambient index) =
    equiv.wires (sourceContext.get index)

private def CertifiedBinderContextsAgree {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (sourceContext : BinderContext source rels)
    (targetContext : BinderContext target rels) : Prop :=
  ∀ binder, targetContext (equiv.regions binder) = sourceContext binder

theorem certifiedAppendContextsAgree
    {source target : ConcreteDiagram}
    {equiv : ConcreteOccurrenceEquiv source target}
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hambient : CertifiedWireContextsAgree equiv
      sourceAmbient targetAmbient ambient)
    (hlocal : CertifiedWireContextsAgree equiv
      sourceLocal targetLocal localEquiv) :
    CertifiedWireContextsAgree equiv (sourceAmbient ++ sourceLocal)
      (targetAmbient ++ targetLocal)
      (appendContextEquiv ambient localEquiv) := by
  intro index
  let sumIndex : Fin (sourceAmbient.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have hindex : Fin.cast (by simp) sumIndex = index := by
    apply Fin.ext
    rfl
  rw [← hindex]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) sumIndex
  · simp only [get_append_castAdd]
    calc
      _ = (targetAmbient ++ targetLocal).get
          (Fin.cast (by simp)
            (Fin.castAdd targetLocal.length (ambient outer))) := by
        congr 1
        apply Fin.ext
        simp [appendContextEquiv, castFinEquiv, extendWireEquiv]
      _ = targetAmbient.get (ambient outer) :=
        get_append_castAdd targetAmbient targetLocal (ambient outer)
      _ = equiv.wires (sourceAmbient.get outer) := hambient outer
  · simp only [get_append_natAdd]
    calc
      _ = (targetAmbient ++ targetLocal).get
          (Fin.cast (by simp)
            (Fin.natAdd targetAmbient.length (localEquiv localIndex))) := by
        congr 1
        apply Fin.ext
        simp [appendContextEquiv, castFinEquiv, extendWireEquiv]
      _ = targetLocal.get (localEquiv localIndex) :=
        get_append_natAdd targetAmbient targetLocal (localEquiv localIndex)
      _ = equiv.wires (sourceLocal.get localIndex) := hlocal localIndex

private theorem CertifiedBinderContextsAgree.push
    {source target : ConcreteDiagram}
    {equiv : ConcreteOccurrenceEquiv source target}
    {sourceContext : BinderContext source rels}
    {targetContext : BinderContext target rels}
    (agrees : CertifiedBinderContextsAgree equiv sourceContext targetContext)
    (binder : Fin source.regionCount) (arity : Nat) :
    CertifiedBinderContextsAgree equiv (sourceContext.push binder arity)
      (targetContext.push (equiv.regions binder) arity) := by
  intro candidate
  by_cases equality : candidate = binder
  · subst candidate
    simp
  · have mappedNe : equiv.regions candidate ≠ equiv.regions binder :=
      fun mappedEq => equality (equiv.regions.injective mappedEq)
    rw [BinderContext.push_other _ arity mappedNe,
      BinderContext.push_other _ arity equality, agrees]

private def certifiedExtendedContextEquiv {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (sourceContext.extend region).length)
      (Fin (targetContext.extend (equiv.regions region)).length) :=
  castFinEquiv (WireContext.length_extend sourceContext region)
    (WireContext.length_extend targetContext (equiv.regions region))
    (extendWireEquiv ambient (certifiedLocalWireEquiv equiv region))

private theorem certifiedAppendWireContextsAgree
    {source target : ConcreteDiagram}
    {equiv : ConcreteOccurrenceEquiv source target}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (agrees : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (region : Fin source.regionCount) :
    ∀ index : Fin
        (sourceContext.length + (exactScopeWires source region).length),
      (targetContext ++ exactScopeWires target (equiv.regions region)).get
          (Fin.cast (by simp)
            (extendWireEquiv ambient
              (certifiedLocalWireEquiv equiv region) index)) =
        equiv.wires
          ((sourceContext ++ exactScopeWires source region).get
            (Fin.cast (by simp) index)) := by
  intro index
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) index
  · rw [extendWireEquiv_outer, get_append_castAdd, get_append_castAdd]
    exact agrees outer
  · rw [extendWireEquiv_local, get_append_natAdd, get_append_natAdd]
    exact certifiedLocalWireEquiv_spec equiv region localIndex

private theorem CertifiedWireContextsAgree.extend
    {source target : ConcreteDiagram}
    {equiv : ConcreteOccurrenceEquiv source target}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (agrees : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (region : Fin source.regionCount) :
    CertifiedWireContextsAgree equiv
      (sourceContext.extend region)
      (targetContext.extend (equiv.regions region))
      (certifiedExtendedContextEquiv equiv sourceContext targetContext
        ambient region) := by
  intro index
  let sourceIndex : Fin
      (sourceContext.length + (exactScopeWires source region).length) :=
    Fin.cast (WireContext.length_extend sourceContext region) index
  have h := certifiedAppendWireContextsAgree agrees region sourceIndex
  change (targetContext ++ exactScopeWires target (equiv.regions region)).get
      (Fin.cast
        (WireContext.length_extend targetContext (equiv.regions region)).symm
        (extendWireEquiv ambient (certifiedLocalWireEquiv equiv region)
          sourceIndex)) =
    equiv.wires ((sourceContext ++ exactScopeWires source region).get index)
  have hsource : Fin.cast (by simp) sourceIndex = index := by
    apply Fin.ext
    rfl
  calc
    _ = equiv.wires ((sourceContext ++ exactScopeWires source region).get
        (Fin.cast (by simp) sourceIndex)) := h
    _ = _ := congrArg equiv.wires (congrArg
      (sourceContext ++ exactScopeWires source region).get hsource)

private theorem certifiedResolvePort?_equivariant
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (htarget : target.WellFormed signature)
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (agrees : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    (node : Fin source.nodeCount) (port : CPort)
    {sourceIndex : Fin sourceContext.length}
    {targetIndex : Fin targetContext.length}
    (hsource : resolvePort? source sourceContext node port = some sourceIndex)
    (htargetResult : resolvePort? target targetContext (equiv.nodes node) port =
      some targetIndex) :
    ambient sourceIndex = targetIndex := by
  obtain ⟨sourceWire, hsourceOccurs, hsourceValue⟩ := resolvePort?_sound hsource
  obtain ⟨targetWire, htargetOccurs, htargetValue⟩ :=
    resolvePort?_sound htargetResult
  have hmappedOccurs : target.EndpointOccurs (equiv.wires sourceWire)
      ⟨equiv.nodes node, port⟩ := by
    simpa only [CEndpoint.rename] using
      equiv.endpointOccurs_transport hsourceOccurs
  have hwire : equiv.wires sourceWire = targetWire :=
    endpoint_wire_unique htarget.wire_endpoints_are_disjoint
      hmappedOccurs htargetOccurs
  have hvalues : targetContext.get (ambient sourceIndex) =
      targetContext.get targetIndex := by
    rw [agrees]
    have hsourceGet : sourceContext.get sourceIndex = sourceWire := by
      simpa only [List.get_eq_getElem] using hsourceValue
    have htargetGet : targetContext.get targetIndex = targetWire := by
      simpa only [List.get_eq_getElem] using htargetValue
    rw [hsourceGet, hwire, htargetGet]
  apply Fin.ext
  exact (List.getElem_inj htargetNodup).mp (by
    simpa only [List.get_eq_getElem] using hvalues)

private theorem certifiedResolvePorts?_equivariant
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (htarget : target.WellFormed signature)
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (agrees : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    (node : Fin source.nodeCount) (arity : Nat) (port : Fin arity → CPort)
    {sourceResult : Fin arity → Fin sourceContext.length}
    {targetResult : Fin arity → Fin targetContext.length}
    (hsource : resolvePorts? source sourceContext node arity port =
      some sourceResult)
    (htargetResult : resolvePorts? target targetContext (equiv.nodes node)
      arity port = some targetResult) :
    ambient.toFun ∘ sourceResult = targetResult := by
  funext index
  exact certifiedResolvePort?_equivariant equiv htarget agrees htargetNodup
    node (port index) (sequenceFin_sound hsource index)
    (sequenceFin_sound htargetResult index)

private theorem compileNode?_certifiedEquivariant
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (htarget : target.WellFormed signature)
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : CertifiedBinderContextsAgree equiv sourceBinders targetBinders)
    (node : Fin source.nodeCount)
    {sourceItem : Item signature sourceContext.length rels}
    {targetItem : Item signature targetContext.length rels}
    (hsource : compileNode? signature source sourceContext sourceBinders node =
      some sourceItem)
    (htargetResult : compileNode? signature target targetContext targetBinders
      (equiv.nodes node) = some targetItem) :
    ItemBetaEtaEquiv signature ambient rels sourceItem targetItem := by
  unfold compileNode? at hsource htargetResult
  generalize hsourceNode : source.nodes node = sourceNode at hsource
  generalize htargetNode : target.nodes (equiv.nodes node) = targetNode
    at htargetResult
  have correspondence := equiv.nodes_correspond node
  rw [hsourceNode, htargetNode] at correspondence
  cases correspondence with
  | term sourceRegion targetRegion ports sourceTerm targetTerm
      region_eq certificate =>
      simp only at hsource htargetResult
      cases hsourceOutput : resolvePort? source sourceContext node .output with
      | none => simp [hsourceOutput] at hsource
      | some sourceOutput =>
          cases hsourceFree : resolvePorts? source sourceContext node ports
              (fun index => .free index) with
          | none => simp [hsourceOutput, hsourceFree] at hsource
          | some sourceFree =>
              simp [hsourceOutput, hsourceFree] at hsource
              subst sourceItem
              cases htargetOutput : resolvePort? target targetContext
                  (equiv.nodes node) .output with
              | none => simp [htargetOutput] at htargetResult
              | some targetOutput =>
                  cases htargetFree : resolvePorts? target targetContext
                      (equiv.nodes node) ports (fun index => .free index) with
                  | none => simp [htargetOutput, htargetFree] at htargetResult
                  | some targetFree =>
                      simp [htargetOutput, htargetFree] at htargetResult
                      subst targetItem
                      apply ItemBetaEtaEquiv.equation
                      · exact certifiedResolvePort?_equivariant equiv htarget
                          hwires htargetNodup node .output
                          hsourceOutput htargetOutput
                      · rw [Lambda.Term.mapFree_comp]
                        have free_eq := certifiedResolvePorts?_equivariant
                          equiv htarget hwires htargetNodup node ports
                          (fun index => .free index) hsourceFree htargetFree
                        rw [free_eq]
                        exact certificate.positionalBetaEta.mapFree targetFree
  | atom sourceRegion sourceBinder targetRegion targetBinder
      region_eq binder_eq =>
      simp only at hsource htargetResult
      cases hsourceRelation : sourceBinders sourceBinder with
      | none => simp [hsourceRelation] at hsource
      | some sourceRelation =>
          have htargetRelation : targetBinders targetBinder = some sourceRelation := by
            rw [← binder_eq, hbinders, hsourceRelation]
          cases sourceRelation with
          | mk arity relation =>
              cases hsourceArguments : resolvePorts? source sourceContext node
                  arity (fun index => .arg index) with
              | none => simp [hsourceRelation, hsourceArguments] at hsource
              | some sourceArguments =>
                  simp [hsourceRelation, hsourceArguments] at hsource
                  subst sourceItem
                  cases htargetArguments : resolvePorts? target targetContext
                      (equiv.nodes node) arity (fun index => .arg index) with
                  | none =>
                      simp [htargetRelation, htargetArguments] at htargetResult
                  | some targetArguments =>
                      simp [htargetRelation, htargetArguments] at htargetResult
                      subst targetItem
                      exact .atom relation (certifiedResolvePorts?_equivariant
                        equiv htarget hwires htargetNodup node arity
                        (fun index => .arg index)
                        hsourceArguments htargetArguments)
  | named sourceRegion targetRegion definition arity region_eq =>
      simp only at hsource htargetResult
      cases hrelation : namedRel? signature definition arity with
      | none => simp [hrelation] at hsource
      | some relation =>
          cases hsourceArguments : resolvePorts? source sourceContext node arity
              (fun index => .arg index) with
          | none => simp [hrelation, hsourceArguments] at hsource
          | some sourceArguments =>
              simp [hrelation, hsourceArguments] at hsource
              subst sourceItem
              cases htargetArguments : resolvePorts? target targetContext
                  (equiv.nodes node) arity (fun index => .arg index) with
              | none => simp [hrelation, htargetArguments] at htargetResult
              | some targetArguments =>
                  simp [hrelation, htargetArguments] at htargetResult
                  subst targetItem
                  exact .named relation (certifiedResolvePorts?_equivariant
                    equiv htarget hwires htargetNodup node arity
                    (fun index => .arg index)
                    hsourceArguments htargetArguments)

theorem regionBetaEtaEquiv_of_cast
    {sourceOuter targetOuter sourceLocal targetLocal
      sourceExtended targetExtended : Nat}
    (sourceEq : sourceExtended = sourceOuter + sourceLocal)
    (targetEq : targetExtended = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq signature sourceExtended rels)
    (targetItems : ItemSeq signature targetExtended rels)
    (hitems : ItemSeqBetaEtaEquiv signature
      (castFinEquiv sourceEq targetEq
        (extendWireEquiv ambient localEquiv)) rels sourceItems targetItems) :
    RegionBetaEtaEquiv signature ambient rels
      (.mk sourceLocal (sourceItems.castWiresEq sourceEq))
      (.mk targetLocal (targetItems.castWiresEq targetEq)) := by
  subst sourceExtended
  subst targetExtended
  simpa using RegionBetaEtaEquiv.mk localEquiv hitems

private theorem compileRegion?_certifiedEquivariant
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (htarget : target.WellFormed signature)
    {sourceFuel targetFuel : Nat} {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (htargetExact : (targetContext.extend (equiv.regions region)).Exact
      (equiv.regions region))
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : CertifiedBinderContextsAgree equiv sourceBinders targetBinders)
    {sourceBody : Region signature sourceContext.length rels}
    {targetBody : Region signature targetContext.length rels}
    (hsource : compileRegion? signature source sourceFuel region sourceContext
      sourceBinders = some sourceBody)
    (htargetResult : compileRegion? signature target targetFuel
      (equiv.regions region) targetContext targetBinders = some targetBody) :
    RegionBetaEtaEquiv signature ambient rels sourceBody targetBody := by
  induction sourceFuel generalizing targetFuel region sourceContext
      targetContext rels sourceBinders targetBinders sourceBody targetBody with
  | zero => simp [compileRegion?] at hsource
  | succ sourceFuel ih =>
      cases targetFuel with
      | zero => simp [compileRegion?] at htargetResult
      | succ targetFuel =>
          let sourceExtended := sourceContext.extend region
          let targetExtended := targetContext.extend (equiv.regions region)
          let extended := certifiedExtendedContextEquiv equiv sourceContext
            targetContext ambient region
          have hwiresExtended : CertifiedWireContextsAgree equiv
              sourceExtended targetExtended extended := by
            exact CertifiedWireContextsAgree.extend hwires region
          have hoccurrence : ∀
              (occurrence : LocalOccurrence source.regionCount source.nodeCount)
              (_ : occurrence ∈ localOccurrences source region)
              (sourceItem : Item signature sourceExtended.length rels)
              (targetItem : Item signature targetExtended.length rels),
              compileOccurrenceWith? signature source
                  (compileRegion? signature source sourceFuel) sourceExtended
                  sourceBinders occurrence = some sourceItem →
              compileOccurrenceWith? signature target
                  (compileRegion? signature target targetFuel) targetExtended
                  targetBinders (certifiedRenameOccurrence equiv occurrence) =
                    some targetItem →
              ItemBetaEtaEquiv signature extended rels sourceItem targetItem := by
            intro occurrence hoccurrenceMem sourceItem targetItem
              hsourceItem htargetItem
            cases occurrence with
            | node node =>
                exact compileNode?_certifiedEquivariant equiv htarget
                  hwiresExtended htargetExact.nodup hbinders node
                  (by simpa [compileOccurrenceWith?] using hsourceItem)
                  (by simpa [compileOccurrenceWith?, certifiedRenameOccurrence]
                    using htargetItem)
            | child child =>
                simp only [certifiedRenameOccurrence, compileOccurrenceWith?]
                  at hsourceItem htargetItem
                have hregionEq := equiv.regions_eq child
                cases hchild : source.regions child with
                | sheet =>
                    rw [hchild] at hregionEq
                    simp only [CRegion.rename] at hregionEq
                    simp [hchild] at hsourceItem
                | cut parent =>
                    have hparentSource :=
                      (mem_localOccurrences_child source region child).mp
                        hoccurrenceMem
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparentSource
                    subst parent
                    rw [hchild] at hregionEq
                    simp only [CRegion.rename] at hregionEq
                    have hparentTarget :
                        (target.regions (equiv.regions child)).parent? =
                          some (equiv.regions region) := by
                      rw [← hregionEq]
                      rfl
                    have hchildExact :=
                      htargetExact.extend_child htarget hparentTarget
                    rw [← hregionEq] at htargetItem
                    simp only [hchild] at hsourceItem htargetItem
                    cases hsourceBody : compileRegion? signature source
                        sourceFuel child sourceExtended sourceBinders with
                    | none => simp [hsourceBody] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceBody] at hsourceItem
                        subst sourceItem
                        cases htargetBody : compileRegion? signature target
                            targetFuel (equiv.regions child) targetExtended
                            targetBinders with
                        | none => simp [htargetBody] at htargetItem
                        | some compiledTarget =>
                            simp [htargetBody] at htargetItem
                            subst targetItem
                            exact .cut (ih hwiresExtended hchildExact hbinders
                              hsourceBody htargetBody)
                | bubble parent arity =>
                    have hparentSource :=
                      (mem_localOccurrences_child source region child).mp
                        hoccurrenceMem
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparentSource
                    subst parent
                    rw [hchild] at hregionEq
                    simp only [CRegion.rename] at hregionEq
                    have hparentTarget :
                        (target.regions (equiv.regions child)).parent? =
                          some (equiv.regions region) := by
                      rw [← hregionEq]
                      rfl
                    have hchildExact :=
                      htargetExact.extend_child htarget hparentTarget
                    have hchildBinders := hbinders.push child arity
                    rw [← hregionEq] at htargetItem
                    simp only [hchild] at hsourceItem htargetItem
                    cases hsourceBody : compileRegion? signature source
                        sourceFuel child sourceExtended
                        (sourceBinders.push child arity) with
                    | none => simp [hsourceBody] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceBody] at hsourceItem
                        subst sourceItem
                        cases htargetBody : compileRegion? signature target
                            targetFuel (equiv.regions child) targetExtended
                            (targetBinders.push (equiv.regions child) arity) with
                        | none => simp [htargetBody] at htargetItem
                        | some compiledTarget =>
                            simp [htargetBody] at htargetItem
                            subst targetItem
                            exact .bubble (ih hwiresExtended hchildExact
                              hchildBinders hsourceBody htargetBody)
          simp only [compileRegion?] at hsource htargetResult
          cases hsourceItems : compileOccurrencesWith? signature source
              (compileRegion? signature source sourceFuel) sourceExtended
              sourceBinders (localOccurrences source region) with
          | none => simp [sourceExtended, hsourceItems] at hsource
          | some sourceItems =>
              simp [sourceExtended, hsourceItems] at hsource
              subst sourceBody
              cases htargetItems : compileOccurrencesWith? signature target
                  (compileRegion? signature target targetFuel) targetExtended
                  targetBinders
                  (localOccurrences target (equiv.regions region)) with
              | none => simp [targetExtended, htargetItems] at htargetResult
              | some targetItems =>
                  simp [targetExtended, htargetItems] at htargetResult
                  subst targetBody
                  have hsourceLength := compileOccurrencesWith?_length
                    (compileRegion? signature source sourceFuel) sourceExtended
                    sourceBinders hsourceItems
                  have htargetLength := compileOccurrencesWith?_length
                    (compileRegion? signature target targetFuel) targetExtended
                    targetBinders htargetItems
                  let positions : FiniteEquiv (Fin sourceItems.length)
                      (Fin targetItems.length) :=
                    castFinEquiv hsourceLength htargetLength
                      (certifiedLocalOccurrenceEquiv equiv region)
                  have hitems : ItemSeqBetaEtaEquiv signature extended rels
                      sourceItems targetItems := by
                    apply ItemSeqBetaEtaEquiv.permute positions
                    intro sourceIndex
                    let occurrenceIndex :
                        Fin (localOccurrences source region).length :=
                      Fin.cast hsourceLength sourceIndex
                    let targetOccurrenceIndex :=
                      certifiedLocalOccurrenceEquiv equiv region occurrenceIndex
                    have hsourceGet := compileOccurrencesWith?_get
                      (compileRegion? signature source sourceFuel) sourceExtended
                      sourceBinders hsourceItems occurrenceIndex
                    have htargetGet := compileOccurrencesWith?_get
                      (compileRegion? signature target targetFuel) targetExtended
                      targetBinders htargetItems targetOccurrenceIndex
                    rw [certifiedLocalOccurrenceEquiv_spec equiv region
                      occurrenceIndex] at htargetGet
                    have hsourcePosition : Fin.cast hsourceLength.symm
                        occurrenceIndex = sourceIndex := by
                      apply Fin.ext
                      rfl
                    have htargetPosition : Fin.cast htargetLength.symm
                        targetOccurrenceIndex = positions sourceIndex := by
                      apply Fin.ext
                      rfl
                    rw [hsourcePosition] at hsourceGet
                    rw [htargetPosition] at htargetGet
                    exact hoccurrence _ (List.get_mem _ _) _ _
                      hsourceGet htargetGet
                  simpa only [finishRegion, sourceExtended, targetExtended,
                    extended, certifiedExtendedContextEquiv] using
                    regionBetaEtaEquiv_of_cast
                      (WireContext.length_extend sourceContext region)
                      (WireContext.length_extend targetContext
                        (equiv.regions region))
                      ambient (certifiedLocalWireEquiv equiv region)
                      sourceItems targetItems hitems

theorem compileRoot?_certifiedEquivariant
    {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target)
    (htarget : target.WellFormed signature)
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hwires : CertifiedWireContextsAgree equiv
      (sourceAmbient ++ sourceLocal) (targetAmbient ++ targetLocal)
      (appendContextEquiv ambient localEquiv))
    (htargetExact : WireContext.Exact
      (targetAmbient ++ targetLocal) target.root)
    {sourceBody : Region signature sourceAmbient.length []}
    {targetBody : Region signature targetAmbient.length []}
    (hsource : compileRoot? signature source sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot? signature target targetAmbient targetLocal =
      some targetBody) :
    RegionBetaEtaEquiv signature ambient [] sourceBody targetBody := by
  let sourceRoot := sourceAmbient ++ sourceLocal
  let targetRoot := targetAmbient ++ targetLocal
  let rootEquiv := appendContextEquiv ambient localEquiv
  have htargetExactMapped : WireContext.Exact targetRoot
      (equiv.regions source.root) := by
    simpa only [targetRoot, equiv.root_eq] using htargetExact
  have hbinders : CertifiedBinderContextsAgree equiv
      (BinderContext.empty : BinderContext source [])
      (BinderContext.empty : BinderContext target []) := by
    intro _
    rfl
  have hoccurrence : ∀
      (occurrence : LocalOccurrence source.regionCount source.nodeCount)
      (_ : occurrence ∈ localOccurrences source source.root)
      (sourceItem : Item signature sourceRoot.length [])
      (targetItem : Item signature targetRoot.length []),
      compileOccurrenceWith? signature source
          (compileRegion? signature source source.regionCount)
          sourceRoot BinderContext.empty occurrence = some sourceItem →
      compileOccurrenceWith? signature target
          (compileRegion? signature target source.regionCount)
          targetRoot BinderContext.empty
          (certifiedRenameOccurrence equiv occurrence) = some targetItem →
      ItemBetaEtaEquiv signature rootEquiv [] sourceItem targetItem := by
    intro occurrence hoccurrenceMem sourceItem targetItem
      hsourceItem htargetItem
    cases occurrence with
    | node node =>
        exact compileNode?_certifiedEquivariant equiv htarget hwires
          htargetExact.nodup hbinders node
          (by simpa [sourceRoot, compileOccurrenceWith?] using hsourceItem)
          (by simpa [targetRoot, compileOccurrenceWith?,
            certifiedRenameOccurrence] using htargetItem)
    | child child =>
        simp only [certifiedRenameOccurrence, compileOccurrenceWith?]
          at hsourceItem htargetItem
        have hregionEq := equiv.regions_eq child
        cases hchild : source.regions child with
        | sheet =>
            rw [hchild] at hregionEq
            simp only [CRegion.rename] at hregionEq
            simp [hchild] at hsourceItem
        | cut parent =>
            have hparentSource :=
              (mem_localOccurrences_child source source.root child).mp
                hoccurrenceMem
            have hparentEq : parent = source.root := by
              simpa [hchild, CRegion.parent?] using hparentSource
            subst parent
            rw [hchild] at hregionEq
            simp only [CRegion.rename] at hregionEq
            have hparentTarget :
                (target.regions (equiv.regions child)).parent? =
                  some (equiv.regions source.root) := by
              rw [← hregionEq]
              rfl
            have hchildExact :=
              htargetExactMapped.extend_child htarget hparentTarget
            rw [← hregionEq] at htargetItem
            simp only [hchild] at hsourceItem htargetItem
            cases hsourceBody : compileRegion? signature source
                source.regionCount child sourceRoot BinderContext.empty with
            | none => simp [hsourceBody] at hsourceItem
            | some compiledSource =>
                simp [hsourceBody] at hsourceItem
                subst sourceItem
                cases htargetBody : compileRegion? signature target
                    source.regionCount (equiv.regions child) targetRoot
                    BinderContext.empty with
                | none => simp [htargetBody] at htargetItem
                | some compiledTarget =>
                    simp [htargetBody] at htargetItem
                    subst targetItem
                    exact .cut (compileRegion?_certifiedEquivariant equiv
                      htarget hwires hchildExact hbinders
                      hsourceBody htargetBody)
        | bubble parent arity =>
            have hparentSource :=
              (mem_localOccurrences_child source source.root child).mp
                hoccurrenceMem
            have hparentEq : parent = source.root := by
              simpa [hchild, CRegion.parent?] using hparentSource
            subst parent
            rw [hchild] at hregionEq
            simp only [CRegion.rename] at hregionEq
            have hparentTarget :
                (target.regions (equiv.regions child)).parent? =
                  some (equiv.regions source.root) := by
              rw [← hregionEq]
              rfl
            have hchildExact :=
              htargetExactMapped.extend_child htarget hparentTarget
            have hchildBinders := hbinders.push child arity
            rw [← hregionEq] at htargetItem
            simp only [hchild] at hsourceItem htargetItem
            cases hsourceBody : compileRegion? signature source
                source.regionCount child sourceRoot
                (BinderContext.empty.push child arity) with
            | none => simp [hsourceBody] at hsourceItem
            | some compiledSource =>
                simp [hsourceBody] at hsourceItem
                subst sourceItem
                cases htargetBody : compileRegion? signature target
                    source.regionCount (equiv.regions child) targetRoot
                    (BinderContext.empty.push (equiv.regions child) arity) with
                | none => simp [htargetBody] at htargetItem
                | some compiledTarget =>
                    simp [htargetBody] at htargetItem
                    subst targetItem
                    exact .bubble (compileRegion?_certifiedEquivariant equiv
                      htarget hwires hchildExact hchildBinders
                      hsourceBody htargetBody)
  simp only [compileRoot?] at hsource htargetResult
  rw [← equiv.regionCount_eq, ← equiv.root_eq] at htargetResult
  cases hsourceItems : compileOccurrencesWith? signature source
      (compileRegion? signature source source.regionCount)
      sourceRoot BinderContext.empty
      (localOccurrences source source.root) with
  | none => simp [sourceRoot, hsourceItems] at hsource
  | some sourceItems =>
      simp [sourceRoot, hsourceItems] at hsource
      subst sourceBody
      cases htargetItems : compileOccurrencesWith? signature target
          (compileRegion? signature target source.regionCount)
          targetRoot BinderContext.empty
          (localOccurrences target (equiv.regions source.root)) with
      | none => simp [targetRoot, htargetItems] at htargetResult
      | some targetItems =>
          simp [targetRoot, htargetItems] at htargetResult
          subst targetBody
          have hsourceLength := compileOccurrencesWith?_length
            (compileRegion? signature source source.regionCount)
            sourceRoot BinderContext.empty hsourceItems
          have htargetLength := compileOccurrencesWith?_length
            (compileRegion? signature target source.regionCount)
            targetRoot BinderContext.empty htargetItems
          let positions : FiniteEquiv (Fin sourceItems.length)
              (Fin targetItems.length) :=
            castFinEquiv hsourceLength htargetLength
              (certifiedLocalOccurrenceEquiv equiv source.root)
          have hitems : ItemSeqBetaEtaEquiv signature rootEquiv []
              sourceItems targetItems := by
            apply ItemSeqBetaEtaEquiv.permute positions
            intro sourceIndex
            let occurrenceIndex :
                Fin (localOccurrences source source.root).length :=
              Fin.cast hsourceLength sourceIndex
            let targetOccurrenceIndex :=
              certifiedLocalOccurrenceEquiv equiv source.root occurrenceIndex
            have hsourceGet := compileOccurrencesWith?_get
              (compileRegion? signature source source.regionCount)
              sourceRoot BinderContext.empty hsourceItems occurrenceIndex
            have htargetGet := compileOccurrencesWith?_get
              (compileRegion? signature target source.regionCount)
              targetRoot BinderContext.empty htargetItems targetOccurrenceIndex
            rw [certifiedLocalOccurrenceEquiv_spec equiv source.root
              occurrenceIndex] at htargetGet
            have hsourcePosition : Fin.cast hsourceLength.symm
                occurrenceIndex = sourceIndex := by
              apply Fin.ext
              rfl
            have htargetPosition : Fin.cast htargetLength.symm
                targetOccurrenceIndex = positions sourceIndex := by
              apply Fin.ext
              rfl
            rw [hsourcePosition] at hsourceGet
            rw [htargetPosition] at htargetGet
            exact hoccurrence _ (List.get_mem _ _) _ _
              hsourceGet htargetGet
          simpa only [finishRoot, sourceRoot, targetRoot, rootEquiv] using
            regionBetaEtaEquiv_of_cast (by simp [sourceRoot])
              (by simp [targetRoot]) ambient localEquiv
              sourceItems targetItems hitems

namespace ConcreteIso

theorem elaborate_isomorphic {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (hsource : source.WellFormed signature)
    (htarget : target.WellFormed signature) :
    Core.Isomorphic (source.elaborate hsource) (target.elaborate htarget) := by
  obtain ⟨sourceBody, hsourceKernel, hsourceElaborate⟩ :=
    ConcreteDiagram.elaborate_computation source hsource
  obtain ⟨targetBody, htargetKernel, htargetElaborate⟩ :=
    ConcreteDiagram.elaborate_computation target htarget
  have htargetKernel' := htargetKernel
  rw [<- iso.root_eq] at htargetKernel'
  have hambient : ConcreteElaboration.WireContextsAgree iso
      ([] : ConcreteElaboration.WireContext source)
      ([] : ConcreteElaboration.WireContext target) (.refl (Fin 0)) := by
    intro index
    exact Fin.elim0 index
  have hlocal : ConcreteElaboration.WireContextsAgree iso
      (ConcreteElaboration.exactScopeWires source source.root)
      (ConcreteElaboration.exactScopeWires target (iso.regions source.root))
      (ConcreteElaboration.localWireEquiv iso source.root) := by
    exact ConcreteElaboration.localWireEquiv_spec iso source.root
  have hwires := ConcreteElaboration.appendContextsAgree hambient hlocal
  have htargetExact : ConcreteElaboration.WireContext.Exact
      (([] : ConcreteElaboration.WireContext target) ++
        ConcreteElaboration.exactScopeWires target
          (iso.regions source.root)) target.root := by
    rw [iso.root_eq]
    exact ConcreteElaboration.closedRootWires_exact htarget
  have hbody : RegionIso signature (.refl (Fin 0)) [] sourceBody targetBody :=
    ConcreteElaboration.compileRoot?_equivariant iso htarget hwires
      htargetExact hsourceKernel htargetKernel'
  rw [hsourceElaborate, htargetElaborate]
  exact hbody

end ConcreteIso

namespace OpenConcreteIso

/-- Ordered open concrete isomorphism commutes with checked elaboration. -/
def elaborate_isomorphic {source target : OpenConcreteDiagram}
    (iso : OpenConcreteIso source target)
    (hsource : source.WellFormed signature)
    (htarget : target.WellFormed signature) :
    OpenDiagramIso (source.elaborate hsource)
      ((target.elaborate htarget).castArity
        iso.boundary_length_eq.symm) := by
  have hambient : ConcreteElaboration.WireContextsAgree iso.diagram
      source.exposedWires target.exposedWires iso.exposedWiresEquiv :=
    iso.exposedWiresEquiv_spec
  have hlocal : ConcreteElaboration.WireContextsAgree iso.diagram
      source.hiddenWires target.hiddenWires iso.hiddenWiresEquiv :=
    iso.hiddenWiresEquiv_spec
  have hwires := ConcreteElaboration.appendContextsAgree hambient hlocal
  have htargetExact : ConcreteElaboration.WireContext.Exact
      (target.exposedWires ++ target.hiddenWires) target.diagram.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      ConcreteElaboration.openRootWires_exact htarget
  have hbody : RegionIso signature iso.exposedWiresEquiv []
      (source.elaborate hsource).body (target.elaborate htarget).body := by
    obtain ⟨sourceBody, hsourceKernel, hsourceElaborate⟩ :=
      CheckedOpenDiagram.elaborate_body_computation
        (show CheckedOpenDiagram signature from ⟨source, hsource⟩)
    obtain ⟨targetBody, htargetKernel, htargetElaborate⟩ :=
      CheckedOpenDiagram.elaborate_body_computation
        (show CheckedOpenDiagram signature from ⟨target, htarget⟩)
    change (source.elaborate hsource).body = sourceBody at hsourceElaborate
    change (target.elaborate htarget).body = targetBody at htargetElaborate
    rw [hsourceElaborate, htargetElaborate]
    exact ConcreteElaboration.compileRoot?_equivariant iso.diagram
      htarget.diagram_well_formed hwires htargetExact
      hsourceKernel htargetKernel
  apply OpenDiagramIso.ofArityEq iso.boundary_length_eq
    iso.exposedWiresEquiv
  · intro position
    simpa only [OpenConcreteDiagram.elaborate_boundary] using
      iso.boundaryClass_commute position
  · exact hbody

end OpenConcreteIso

end VisualProof.Diagram
