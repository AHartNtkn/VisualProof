import VisualProof.Concrete.Elaboration.Compile.Elaborate

namespace VisualProof.Concrete

open VisualProof.Diagram

open Elaboration
open VisualProof.Data.Finite
open VisualProof.Theory

private theorem certifiedExactScopeWires_mem_iff
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
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

private def certifiedLocalWireEquiv {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (exactScopeWires source region).length)
      (Fin (exactScopeWires target (equiv.regions region)).length) :=
  FiniteEquiv.restrictLists equiv.wires _ _
    (exactScopeWires_nodup source region)
    (exactScopeWires_nodup target (equiv.regions region))
    (certifiedExactScopeWires_mem_iff equiv region)

private theorem certifiedLocalWireEquiv_spec
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (region : Fin source.regionCount)
    (index : Fin (exactScopeWires source region).length) :
    (exactScopeWires target (equiv.regions region)).get
        (certifiedLocalWireEquiv equiv region index) =
      equiv.wires ((exactScopeWires source region).get index) :=
  FiniteEquiv.restrictLists_spec equiv.wires _ _ _ _ _ index

private theorem certifiedLocalOccurrences_mem_iff
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
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

private def certifiedLocalOccurrenceEquiv {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (localOccurrences source region).length)
      (Fin (localOccurrences target (equiv.regions region)).length) :=
  FiniteEquiv.restrictLists (certifiedOccurrenceEquiv equiv) _ _
    (localOccurrences_nodup source region)
    (localOccurrences_nodup target (equiv.regions region))
    (certifiedLocalOccurrences_mem_iff equiv region)

private theorem certifiedLocalOccurrenceEquiv_spec
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (region : Fin source.regionCount)
    (index : Fin (localOccurrences source region).length) :
    (localOccurrences target (equiv.regions region)).get
        (certifiedLocalOccurrenceEquiv equiv region index) =
      certifiedRenameOccurrence equiv
        ((localOccurrences source region).get index) :=
  FiniteEquiv.restrictLists_spec (certifiedOccurrenceEquiv equiv) _ _ _ _ _ index

def CertifiedWireContextsAgree {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)) : Prop :=
  ∀ index, targetContext.get (ambient index) =
    equiv.wires (sourceContext.get index)

private def CertifiedBinderContextsAgree {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (sourceContext : BinderContext source rels)
    (targetContext : BinderContext target rels) : Prop :=
  ∀ binder, targetContext (equiv.regions binder) = sourceContext binder

theorem certifiedAppendContextsAgree
    {source target : Diagram}
    {equiv : OccurrenceEquiv source target}
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
    {source target : Diagram}
    {equiv : OccurrenceEquiv source target}
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

private def certifiedExtendedContextEquiv {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
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
    {source target : Diagram}
    {equiv : OccurrenceEquiv source target}
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
    {source target : Diagram}
    {equiv : OccurrenceEquiv source target}
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
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (htarget : target.WellFormed )
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
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (htarget : target.WellFormed )
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

private noncomputable def compileNode?_certifiedEquivariant
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (htarget : target.WellFormed )
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : CertifiedBinderContextsAgree equiv sourceBinders targetBinders)
    (node : Fin source.nodeCount)
    {sourceItem : CompiledItem source sourceContext.length rels}
    {targetItem : CompiledItem target targetContext.length rels}
    (hsource : compileNode?  source sourceContext sourceBinders node =
      some sourceItem)
    (htargetResult : compileNode?  target targetContext targetBinders
      (equiv.nodes node) = some targetItem) :
    ItemIso  ambient rels sourceItem.erase targetItem.erase := by
  unfold compileNode? at hsource htargetResult
  generalize hsourceNode : source.nodes node = sourceNode at hsource
  generalize htargetNode : target.nodes (equiv.nodes node) = targetNode
    at htargetResult
  have correspondence := equiv.nodes_correspond node
  rw [hsourceNode, htargetNode] at correspondence
  cases correspondence with
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
  | identity sourceRegion targetRegion arity region_eq =>
      simp only at hsource htargetResult
      cases hsourceArguments : resolvePorts? source sourceContext node arity
          (fun index => .arg index) with
      | none => simp [hsourceArguments] at hsource
      | some sourceArguments =>
          simp [hsourceArguments] at hsource
          subst sourceItem
          cases htargetArguments : resolvePorts? target targetContext
              (equiv.nodes node) arity (fun index => .arg index) with
          | none => simp [htargetArguments] at htargetResult
          | some targetArguments =>
              simp [htargetArguments] at htargetResult
              subst targetItem
              exact .identity (certifiedResolvePorts?_equivariant
                equiv htarget hwires htargetNodup node arity
                (fun index => .arg index)
                hsourceArguments htargetArguments)
noncomputable def regionIso_of_cast
    {sourceOuter targetOuter sourceLocal targetLocal
      sourceExtended targetExtended : Nat}
    (sourceEq : sourceExtended = sourceOuter + sourceLocal)
    (targetEq : targetExtended = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq  sourceExtended rels)
    (targetItems : ItemSeq  targetExtended rels)
    (hitems : ItemSeqIso
      (castFinEquiv sourceEq targetEq
        (extendWireEquiv ambient localEquiv)) rels sourceItems targetItems) :
    RegionIso  ambient rels
      (.mk sourceLocal (sourceItems.castWiresEq sourceEq))
      (.mk targetLocal (targetItems.castWiresEq targetEq)) := by
  subst sourceExtended
  subst targetExtended
  simpa using RegionIso.mk localEquiv hitems

private noncomputable def compileRegion?_certifiedEquivariant
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (htarget : target.WellFormed )
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
    {sourceBody : CompiledRegion source sourceContext.length rels}
    {targetBody : CompiledRegion target targetContext.length rels}
    (hsource : compileRegion?  source sourceFuel region sourceContext
      sourceBinders = some sourceBody)
    (htargetResult : compileRegion?  target targetFuel
      (equiv.regions region) targetContext targetBinders = some targetBody) :
    RegionIso  ambient rels sourceBody.erase targetBody.erase := by
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
              (sourceItem : CompiledItem source sourceExtended.length rels)
              (targetItem : CompiledItem target targetExtended.length rels),
              compileOccurrenceWith?  source
                  (compileRegion?  source sourceFuel) sourceExtended
                  sourceBinders occurrence = some sourceItem →
              compileOccurrenceWith?  target
                  (compileRegion?  target targetFuel) targetExtended
                  targetBinders (certifiedRenameOccurrence equiv occurrence) =
                    some targetItem →
              ItemIso  extended rels sourceItem.erase targetItem.erase := by
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
                    cases hsourceBody : compileRegion?  source
                        sourceFuel child sourceExtended sourceBinders with
                    | none => simp [hsourceBody] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceBody] at hsourceItem
                        subst sourceItem
                        cases htargetBody : compileRegion?  target
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
                    cases hsourceBody : compileRegion?  source
                        sourceFuel child sourceExtended
                        (sourceBinders.push child arity) with
                    | none => simp [hsourceBody] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceBody] at hsourceItem
                        subst sourceItem
                        cases htargetBody : compileRegion?  target
                            targetFuel (equiv.regions child) targetExtended
                            (targetBinders.push (equiv.regions child) arity) with
                        | none => simp [htargetBody] at htargetItem
                        | some compiledTarget =>
                            simp [htargetBody] at htargetItem
                            subst targetItem
                            exact .bubble (ih hwiresExtended hchildExact
                              hchildBinders hsourceBody htargetBody)
          simp only [compileRegion?] at hsource htargetResult
          cases hsourceItems : compileOccurrencesWith?  source
              (compileRegion?  source sourceFuel) sourceExtended
              sourceBinders (localOccurrences source region) with
          | none => simp [sourceExtended, hsourceItems] at hsource
          | some sourceItems =>
              simp [sourceExtended, hsourceItems] at hsource
              subst sourceBody
              cases htargetItems : compileOccurrencesWith?  target
                  (compileRegion?  target targetFuel) targetExtended
                  targetBinders
                  (localOccurrences target (equiv.regions region)) with
              | none => simp [targetExtended, htargetItems] at htargetResult
              | some targetItems =>
                  simp [targetExtended, htargetItems] at htargetResult
                  subst targetBody
                  have hsourceLength := compileOccurrencesWith?_length
                    (compileRegion?  source sourceFuel) sourceExtended
                    sourceBinders hsourceItems
                  have htargetLength := compileOccurrencesWith?_length
                    (compileRegion?  target targetFuel) targetExtended
                    targetBinders htargetItems
                  let positions : FiniteEquiv (Fin sourceItems.length)
                      (Fin targetItems.length) :=
                    castFinEquiv hsourceLength htargetLength
                      (certifiedLocalOccurrenceEquiv equiv region)
                  have hitems : ItemSeqIso  extended rels
                      sourceItems.erase targetItems.erase := by
                    apply ItemSeqIso.permute positions
                    intro sourceIndex
                    let occurrenceIndex :
                        Fin (localOccurrences source region).length :=
                      Fin.cast hsourceLength sourceIndex
                    let targetOccurrenceIndex :=
                      certifiedLocalOccurrenceEquiv equiv region occurrenceIndex
                    have hsourceGet := compileOccurrencesWith?_get
                      (compileRegion?  source sourceFuel) sourceExtended
                      sourceBinders hsourceItems occurrenceIndex
                    have htargetGet := compileOccurrencesWith?_get
                      (compileRegion?  target targetFuel) targetExtended
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
                    simpa only [CompiledItems.erase_get] using
                      hoccurrence _ (List.get_mem _ _) _ _
                        hsourceGet htargetGet
                  simpa only [finishRegion, sourceExtended, targetExtended,
                    extended, certifiedExtendedContextEquiv,
                    CompiledRegion.erase] using
                    regionIso_of_cast
                      (WireContext.length_extend sourceContext region)
                      (WireContext.length_extend targetContext
                        (equiv.regions region))
                      ambient (certifiedLocalWireEquiv equiv region)
                      sourceItems.erase targetItems.erase hitems

noncomputable def compileRoot?_certifiedEquivariant
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (htarget : target.WellFormed )
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
    {sourceBody : CompiledRegion source sourceAmbient.length []}
    {targetBody : CompiledRegion target targetAmbient.length []}
    (hsource : compileRoot?  source sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot?  target targetAmbient targetLocal =
      some targetBody) :
    RegionIso  ambient [] sourceBody.erase targetBody.erase := by
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
      (sourceItem : CompiledItem source sourceRoot.length [])
      (targetItem : CompiledItem target targetRoot.length []),
      compileOccurrenceWith?  source
          (compileRegion?  source source.regionCount)
          sourceRoot BinderContext.empty occurrence = some sourceItem →
      compileOccurrenceWith?  target
          (compileRegion?  target source.regionCount)
          targetRoot BinderContext.empty
          (certifiedRenameOccurrence equiv occurrence) = some targetItem →
      ItemIso  rootEquiv [] sourceItem.erase targetItem.erase := by
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
            cases hsourceBody : compileRegion?  source
                source.regionCount child sourceRoot BinderContext.empty with
            | none => simp [hsourceBody] at hsourceItem
            | some compiledSource =>
                simp [hsourceBody] at hsourceItem
                subst sourceItem
                cases htargetBody : compileRegion?  target
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
            cases hsourceBody : compileRegion?  source
                source.regionCount child sourceRoot
                (BinderContext.empty.push child arity) with
            | none => simp [hsourceBody] at hsourceItem
            | some compiledSource =>
                simp [hsourceBody] at hsourceItem
                subst sourceItem
                cases htargetBody : compileRegion?  target
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
  cases hsourceItems : compileOccurrencesWith?  source
      (compileRegion?  source source.regionCount)
      sourceRoot BinderContext.empty
      (localOccurrences source source.root) with
  | none => simp [sourceRoot, hsourceItems] at hsource
  | some sourceItems =>
      simp [sourceRoot, hsourceItems] at hsource
      subst sourceBody
      cases htargetItems : compileOccurrencesWith?  target
          (compileRegion?  target source.regionCount)
          targetRoot BinderContext.empty
          (localOccurrences target (equiv.regions source.root)) with
      | none => simp [targetRoot, htargetItems] at htargetResult
      | some targetItems =>
          simp [targetRoot, htargetItems] at htargetResult
          subst targetBody
          have hsourceLength := compileOccurrencesWith?_length
            (compileRegion?  source source.regionCount)
            sourceRoot BinderContext.empty hsourceItems
          have htargetLength := compileOccurrencesWith?_length
            (compileRegion?  target source.regionCount)
            targetRoot BinderContext.empty htargetItems
          let positions : FiniteEquiv (Fin sourceItems.length)
              (Fin targetItems.length) :=
            castFinEquiv hsourceLength htargetLength
              (certifiedLocalOccurrenceEquiv equiv source.root)
          have hitems : ItemSeqIso  rootEquiv []
              sourceItems.erase targetItems.erase := by
            apply ItemSeqIso.permute positions
            intro sourceIndex
            let occurrenceIndex :
                Fin (localOccurrences source source.root).length :=
              Fin.cast hsourceLength sourceIndex
            let targetOccurrenceIndex :=
              certifiedLocalOccurrenceEquiv equiv source.root occurrenceIndex
            have hsourceGet := compileOccurrencesWith?_get
              (compileRegion?  source source.regionCount)
              sourceRoot BinderContext.empty hsourceItems occurrenceIndex
            have htargetGet := compileOccurrencesWith?_get
              (compileRegion?  target source.regionCount)
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
            simpa only [CompiledItems.erase_get] using
              hoccurrence _ (List.get_mem _ _) _ _
                hsourceGet htargetGet
          simpa only [finishRoot, sourceRoot, targetRoot, rootEquiv,
            CompiledRegion.erase] using
            regionIso_of_cast (by simp [sourceRoot])
              (by simp [targetRoot]) ambient localEquiv
              sourceItems.erase targetItems.erase hitems

/-- Checked open elaboration retains exactly the hidden root-wire context as
the body's local wires. -/
theorem OpenDiagram.elaborate_body_localCount
    (diagram : OpenDiagram) (wellFormed : diagram.WellFormed) :
    (diagram.elaborate wellFormed).body.localCount =
      diagram.hiddenWires.length := by
  let checked : CheckedOpen := ⟨diagram, wellFormed⟩
  change checked.elaborate.body.localCount = checked.val.hiddenWires.length
  obtain ⟨body, compiled, _, elaborated⟩ :=
    CheckedOpen.elaborate_body_computation checked
  rw [elaborated]
  simpa using Elaboration.compileRoot?_localCount compiled

/-- Transporting only the ordered-boundary arity leaves the elaborated body's
local-wire count unchanged. -/
theorem OpenDiagram.elaborate_castArity_body_localCount
    (diagram : OpenDiagram) (wellFormed : diagram.WellFormed)
    (arityEq : diagram.boundary.length = arity) :
    ((diagram.elaborate wellFormed).castArity arityEq).body.localCount =
      diagram.hiddenWires.length := by
  subst arity
  exact diagram.elaborate_body_localCount wellFormed

namespace Iso

theorem elaborate_isomorphic {source target : Diagram}
    (iso : Iso source target)
    (hsource : source.WellFormed )
    (htarget : target.WellFormed ) :
    Core.Isomorphic (source.elaborate hsource) (target.elaborate htarget) := by
  obtain ⟨sourceBody, hsourceKernel, hsourceElaborate⟩ :=
    Diagram.elaborate_computation source hsource
  obtain ⟨targetBody, htargetKernel, htargetElaborate⟩ :=
    Diagram.elaborate_computation target htarget
  have htargetKernel' := htargetKernel
  rw [<- iso.root_eq] at htargetKernel'
  have hambient : Elaboration.WireContextsAgree iso
      ([] : Elaboration.WireContext source)
      ([] : Elaboration.WireContext target) (.refl (Fin 0)) := by
    intro index
    exact Fin.elim0 index
  have hlocal : Elaboration.WireContextsAgree iso
      (Elaboration.exactScopeWires source source.root)
      (Elaboration.exactScopeWires target (iso.regions source.root))
      (Elaboration.localWireEquiv iso source.root) := by
    exact Elaboration.localWireEquiv_spec iso source.root
  have hwires := Elaboration.appendContextsAgree hambient hlocal
  have htargetExact : Elaboration.WireContext.Exact
      (([] : Elaboration.WireContext target) ++
        Elaboration.exactScopeWires target
          (iso.regions source.root)) target.root := by
    rw [iso.root_eq]
    exact Elaboration.closedRootWires_exact htarget
  have hbody : RegionIso  (.refl (Fin 0)) [] sourceBody.erase targetBody.erase :=
    Elaboration.compileRoot?_equivariant iso htarget hwires
      htargetExact hsourceKernel htargetKernel'
  rw [hsourceElaborate, htargetElaborate]
  exact ⟨hbody⟩

end Iso

private theorem openDiagramIso_ofArityEq_localEquivCast
    {sourceArity targetArity sourceLocal targetLocal : Nat}
    {source : Diagram.OpenDiagram sourceArity}
    {target : Diagram.OpenDiagram targetArity}
    (arityEq : sourceArity = targetArity)
    (external : FiniteEquiv (Fin source.externalClasses)
      (Fin target.externalClasses))
    (boundary : ∀ position,
      external (source.boundary position) =
        target.boundary (Fin.cast arityEq position))
    (body : RegionIso external [] source.body target.body)
    (sourceLocalEq : source.body.localCount = sourceLocal)
    (targetLocalEq : target.body.localCount = targetLocal)
    (castTargetLocalEq :
      (target.castArity arityEq.symm).body.localCount = targetLocal) :
    (OpenDiagramIso.ofArityEq arityEq external boundary body).body.localEquivCast
        sourceLocalEq castTargetLocalEq =
      body.localEquivCast sourceLocalEq targetLocalEq := by
  subst targetArity
  rfl

namespace OpenIso

/-- Ordered open concrete isomorphism commutes with checked elaboration. -/
noncomputable def elaborate_isomorphic {source target : OpenDiagram}
    (iso : OpenIso source target)
    (hsource : source.WellFormed )
    (htarget : target.WellFormed ) :
    OpenDiagramIso (source.elaborate hsource)
      ((target.elaborate htarget).castArity
        iso.boundary_length_eq.symm) := by
  have hambient : Elaboration.WireContextsAgree iso.diagram
      source.exposedWires target.exposedWires iso.exposedWiresEquiv :=
    iso.exposedWiresEquiv_spec
  have hlocal : Elaboration.WireContextsAgree iso.diagram
      source.hiddenWires target.hiddenWires iso.hiddenWiresEquiv :=
    iso.hiddenWiresEquiv_spec
  have hwires := Elaboration.appendContextsAgree hambient hlocal
  have htargetExact : Elaboration.WireContext.Exact
      (target.exposedWires ++ target.hiddenWires) target.diagram.root := by
    simpa only [OpenDiagram.rootWires] using
      Elaboration.openRootWires_exact htarget
  have hbody : RegionIso  iso.exposedWiresEquiv []
      (source.elaborate hsource).body (target.elaborate htarget).body := by
    have hsourceKernel : compileRoot? source.diagram source.exposedWires
        source.hiddenWires =
          some (CheckedOpen.compilation ⟨source, hsource⟩) := by
      obtain ⟨sourceBody, hkernel, hcompilation, _⟩ :=
        CheckedOpen.elaborate_body_computation
          (show CheckedOpen from ⟨source, hsource⟩)
      rw [hcompilation]
      exact hkernel
    have htargetKernel : compileRoot? target.diagram target.exposedWires
        target.hiddenWires =
          some (CheckedOpen.compilation ⟨target, htarget⟩) := by
      obtain ⟨targetBody, hkernel, hcompilation, _⟩ :=
        CheckedOpen.elaborate_body_computation
          (show CheckedOpen from ⟨target, htarget⟩)
      rw [hcompilation]
      exact hkernel
    simpa [OpenDiagram.elaborate, CheckedOpen.elaborate] using
      Elaboration.compileRoot?_equivariant iso.diagram
        htarget.diagram_well_formed hwires htargetExact
        hsourceKernel htargetKernel
  apply OpenDiagramIso.ofArityEq iso.boundary_length_eq
    iso.exposedWiresEquiv
  · intro position
    simpa only [OpenDiagram.elaborate_boundary] using
      iso.boundaryClass_commute position
  · exact hbody

/-- The body witness stored by ordered-open elaboration uses the hidden-wire
equivalence supplied by the concrete open isomorphism. -/
theorem elaborate_isomorphic_localEquivCast {source target : OpenDiagram}
    (iso : OpenIso source target)
    (hsource : source.WellFormed)
    (htarget : target.WellFormed) :
    (iso.elaborate_isomorphic hsource htarget).body.localEquivCast
        (source.elaborate_body_localCount hsource)
        (target.elaborate_castArity_body_localCount htarget
          iso.boundary_length_eq.symm) =
      iso.hiddenWiresEquiv := by
  unfold elaborate_isomorphic
  dsimp only
  rw [openDiagramIso_ofArityEq_localEquivCast]
  · apply Elaboration.compileRoot?_equivariant_localEquivCast
  · exact target.elaborate_body_localCount htarget

end OpenIso

end VisualProof.Concrete
