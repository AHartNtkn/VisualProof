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
    {sourceItem : CompiledItem source sourceContext rels sourceBinders}
    {targetItem : CompiledItem target targetContext rels targetBinders}
    (hsource : compileNode? source sourceContext sourceBinders node =
      some sourceItem)
    (htargetResult : compileNode? target targetContext targetBinders
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

theorem regionIso_of_cast_localEquiv
    {sourceOuter targetOuter sourceLocal targetLocal
      sourceExtended targetExtended : Nat}
    (sourceEq : sourceExtended = sourceOuter + sourceLocal)
    (targetEq : targetExtended = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq sourceExtended rels)
    (targetItems : ItemSeq targetExtended rels)
    (hitems : ItemSeqIso
      (castFinEquiv sourceEq targetEq (extendWireEquiv ambient localEquiv))
      rels sourceItems targetItems) :
    (regionIso_of_cast sourceEq targetEq ambient localEquiv sourceItems
      targetItems hitems).localEquiv = localEquiv := by
  subst sourceExtended
  subst targetExtended
  rfl

private noncomputable def compileItems?_certifiedEquivariant
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (hsourceWellFormed : source.WellFormed)
    (htargetWellFormed : target.WellFormed)
    {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (occurrenceIso : ∀
      (occurrence : LocalOccurrence source.regionCount source.nodeCount),
      (sourceDirect : occurrence ∈ localOccurrences source region) →
      (targetOccurrence :
        LocalOccurrence target.regionCount target.nodeCount) →
      (targetDirect : targetOccurrence ∈
        localOccurrences target (equiv.regions region)) →
      certifiedRenameOccurrence equiv occurrence = targetOccurrence →
      (sourceItem : CompiledItem source sourceContext rels sourceBinders) →
      (targetItem : CompiledItem target targetContext rels targetBinders) →
      compileOccurrence? source hsourceWellFormed region sourceContext
          sourceBinders occurrence sourceDirect = some sourceItem →
      compileOccurrence? target htargetWellFormed (equiv.regions region)
          targetContext targetBinders targetOccurrence targetDirect =
        some targetItem →
      ItemIso ambient rels sourceItem.erase targetItem.erase)
    {sourceItems : CompiledItems source sourceContext rels sourceBinders}
    {targetItems : CompiledItems target targetContext rels targetBinders}
    (hsource : compileItems? source hsourceWellFormed region sourceContext
      sourceBinders (localOccurrences source region) (fun _ member => member) =
        some sourceItems)
    (htarget : compileItems? target htargetWellFormed (equiv.regions region)
      targetContext targetBinders
      (localOccurrences target (equiv.regions region))
      (fun _ member => member) = some targetItems) :
    ItemSeqIso ambient rels sourceItems.erase targetItems.erase := by
  have hsourceLength := compileItems?_length hsourceWellFormed region
    sourceContext sourceBinders hsource
  have htargetLength := compileItems?_length htargetWellFormed
    (equiv.regions region) targetContext targetBinders htarget
  let positions : FiniteEquiv (Fin sourceItems.length)
      (Fin targetItems.length) :=
    castFinEquiv hsourceLength htargetLength
      (certifiedLocalOccurrenceEquiv equiv region)
  apply ItemSeqIso.permute positions
  intro sourceIndex
  let occurrenceIndex : Fin (localOccurrences source region).length :=
    Fin.cast hsourceLength sourceIndex
  let targetOccurrenceIndex :=
    certifiedLocalOccurrenceEquiv equiv region occurrenceIndex
  have hsourceGet := compileItems?_get hsourceWellFormed region sourceContext
    sourceBinders hsource occurrenceIndex
  have htargetGet := compileItems?_get htargetWellFormed
    (equiv.regions region) targetContext targetBinders htarget
    targetOccurrenceIndex
  have hsourcePosition : Fin.cast hsourceLength.symm occurrenceIndex =
      sourceIndex := by
    apply Fin.ext
    rfl
  have htargetPosition : Fin.cast htargetLength.symm targetOccurrenceIndex =
      positions sourceIndex := by
    apply Fin.ext
    rfl
  rw [hsourcePosition] at hsourceGet
  rw [htargetPosition] at htargetGet
  simpa only [CompiledItems.erase_get] using
    occurrenceIso _ (List.get_mem _ _) _ (List.get_mem _ _)
      (certifiedLocalOccurrenceEquiv_spec equiv region occurrenceIndex).symm
      _ _ hsourceGet htargetGet

private noncomputable def compileRegion?_certifiedEquivariant
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (hsourceWellFormed : source.WellFormed)
    (htargetWellFormed : target.WellFormed)
    {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : CertifiedWireContextsAgree equiv sourceContext targetContext ambient)
    (htargetExact : (targetContext.extend (equiv.regions region)).Exact
      (equiv.regions region))
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : CertifiedBinderContextsAgree equiv sourceBinders targetBinders)
    {sourceBody : CompiledRegion source
      (.nested region sourceContext rels sourceBinders)}
    {targetBody : CompiledRegion target
      (.nested (equiv.regions region) targetContext rels targetBinders)}
    (hsource : compileRegion? source hsourceWellFormed region sourceContext
      sourceBinders = some sourceBody)
    (htargetResult : compileRegion? target htargetWellFormed
      (equiv.regions region) targetContext targetBinders = some targetBody) :
    RegionIso ambient rels sourceBody.erase targetBody.erase := by
  let motive : CompilerCall source → Prop := fun call =>
    match call with
    | .root _ _ => True
    | .nested region sourceContext rels sourceBinders =>
        ∀ {targetContext : WireContext target}
          {ambient : FiniteEquiv (Fin sourceContext.length)
            (Fin targetContext.length)},
          CertifiedWireContextsAgree equiv sourceContext targetContext ambient →
          (targetContext.extend (equiv.regions region)).Exact
            (equiv.regions region) →
          ∀ {targetBinders : BinderContext target rels},
          CertifiedBinderContextsAgree equiv sourceBinders targetBinders →
          ∀ {sourceBody : CompiledRegion source
              (.nested region sourceContext rels sourceBinders)}
            {targetBody : CompiledRegion target
              (.nested (equiv.regions region) targetContext rels targetBinders)},
          compileRegion? source hsourceWellFormed region sourceContext
              sourceBinders = some sourceBody →
          compileRegion? target htargetWellFormed (equiv.regions region)
              targetContext targetBinders = some targetBody →
          Nonempty (RegionIso ambient rels sourceBody.erase targetBody.erase)
  have allCalls : ∀ call, motive call :=
    CompilerCall.compile?.induct source hsourceWellFormed motive (by
      intro call
      dsimp only
      intro childIH
      cases call with
      | root =>
          exact True.intro
      | nested region sourceContext rels sourceBinders =>
          intro targetContext ambient hwires htargetExact targetBinders hbinders
            sourceBody targetBody hsource htargetResult
          refine ⟨?_⟩
          let sourceExtended := sourceContext.extend region
          let targetExtended :=
            targetContext.extend (equiv.regions region)
          let extended := certifiedExtendedContextEquiv equiv sourceContext
            targetContext ambient region
          have hwiresExtended : CertifiedWireContextsAgree equiv
              sourceExtended targetExtended extended :=
            CertifiedWireContextsAgree.extend hwires region
          have hoccurrence : ∀
              (occurrence :
                LocalOccurrence source.regionCount source.nodeCount),
              (sourceDirect :
                occurrence ∈ localOccurrences source region) →
              (sourceItem : CompiledItem source sourceExtended rels
                sourceBinders) →
              (targetItem : CompiledItem target targetExtended rels
                targetBinders) →
              compileOccurrence? source hsourceWellFormed region
                  sourceExtended sourceBinders occurrence sourceDirect =
                some sourceItem →
              compileOccurrence? target htargetWellFormed
                  (equiv.regions region) targetExtended targetBinders
                  (certifiedRenameOccurrence equiv occurrence)
                  ((certifiedLocalOccurrences_mem_iff equiv region
                    occurrence).2 sourceDirect) = some targetItem →
              ItemIso extended rels sourceItem.erase targetItem.erase := by
            intro occurrence sourceDirect sourceItem targetItem
              hsourceItem htargetItem
            cases occurrence with
            | node node =>
                exact compileNode?_certifiedEquivariant equiv
                  htargetWellFormed hwiresExtended htargetExact.nodup
                  hbinders node
                  (by simpa only [compileOccurrence?_node] using hsourceItem)
                  (by
                    simpa only [certifiedRenameOccurrence,
                      compileOccurrence?_node] using htargetItem)
            | child child =>
                have hregionEq := equiv.regions_eq child
                have targetDirect :
                    LocalOccurrence.child (equiv.regions child) ∈
                      localOccurrences target (equiv.regions region) :=
                  (certifiedLocalOccurrences_mem_iff equiv region
                    (.child child)).2 sourceDirect
                cases hchild : source.regions child with
                | sheet =>
                    rw [compileOccurrence?_child_sheet hsourceWellFormed
                      region child sourceExtended sourceBinders sourceDirect
                      hchild] at hsourceItem
                    contradiction
                | cut parent =>
                    have hparentSource :=
                      (mem_localOccurrences_child source region child).mp
                        sourceDirect
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
                      htargetExact.extend_child htargetWellFormed hparentTarget
                    simp only [certifiedRenameOccurrence] at htargetItem
                    rw [compileOccurrence?_child_cut hsourceWellFormed region
                      child sourceExtended sourceBinders sourceDirect hchild]
                      at hsourceItem
                    rw [compileOccurrence?_child_cut htargetWellFormed
                      (equiv.regions region) (equiv.regions child)
                      targetExtended targetBinders targetDirect hregionEq.symm]
                      at htargetItem
                    cases hsourceChild : compileRegion? source
                        hsourceWellFormed child sourceExtended sourceBinders with
                    | none => simp [hsourceChild] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceChild] at hsourceItem
                        subst sourceItem
                        cases htargetChild : compileRegion? target
                            htargetWellFormed (equiv.regions child)
                            targetExtended targetBinders with
                        | none => simp [htargetChild] at htargetItem
                        | some compiledTarget =>
                            simp [htargetChild] at htargetItem
                            subst targetItem
                            have hchildIso : Nonempty (RegionIso extended rels
                                compiledSource.erase compiledTarget.erase) :=
                              (childIH child hparentSource sourceExtended
                                sourceBinders) hwiresExtended hchildExact
                                hbinders hsourceChild htargetChild
                            exact .cut (Classical.choice hchildIso)
                | bubble parent arity =>
                    have hparentSource :=
                      (mem_localOccurrences_child source region child).mp
                        sourceDirect
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
                      htargetExact.extend_child htargetWellFormed hparentTarget
                    have hchildBinders := hbinders.push child arity
                    simp only [certifiedRenameOccurrence] at htargetItem
                    rw [compileOccurrence?_child_bubble hsourceWellFormed
                      region child sourceExtended sourceBinders arity
                      sourceDirect hchild] at hsourceItem
                    rw [compileOccurrence?_child_bubble htargetWellFormed
                      (equiv.regions region) (equiv.regions child)
                      targetExtended targetBinders arity targetDirect
                      hregionEq.symm] at htargetItem
                    cases hsourceChild : compileRegion? source
                        hsourceWellFormed child sourceExtended
                        (sourceBinders.push child arity) with
                    | none => simp [hsourceChild] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceChild] at hsourceItem
                        subst sourceItem
                        cases htargetChild : compileRegion? target
                            htargetWellFormed (equiv.regions child)
                            targetExtended
                            (targetBinders.push (equiv.regions child) arity) with
                        | none => simp [htargetChild] at htargetItem
                        | some compiledTarget =>
                            simp [htargetChild] at htargetItem
                            subst targetItem
                            have hchildIso : Nonempty (RegionIso extended
                                (arity :: rels) compiledSource.erase
                                compiledTarget.erase) :=
                              (childIH child hparentSource sourceExtended
                                (sourceBinders.push child arity))
                                hwiresExtended hchildExact hchildBinders
                                hsourceChild htargetChild
                            exact .bubble (Classical.choice hchildIso)
          rw [compileRegion?_eq_compileItems? hsourceWellFormed] at hsource
          rw [compileRegion?_eq_compileItems? htargetWellFormed]
            at htargetResult
          cases hsourceItems : compileItems? source hsourceWellFormed region
              sourceExtended sourceBinders (localOccurrences source region)
              (fun _ member => member) with
          | none => simp [sourceExtended, hsourceItems] at hsource
          | some sourceItems =>
              simp [sourceExtended, hsourceItems] at hsource
              subst sourceBody
              cases htargetItems : compileItems? target htargetWellFormed
                  (equiv.regions region) targetExtended targetBinders
                  (localOccurrences target (equiv.regions region))
                  (fun _ member => member) with
              | none =>
                  simp [targetExtended, htargetItems] at htargetResult
              | some targetItems =>
                  simp [targetExtended, htargetItems] at htargetResult
                  subst targetBody
                  have hitems := compileItems?_certifiedEquivariant equiv
                    hsourceWellFormed htargetWellFormed (by
                      intro occurrence sourceDirect targetOccurrence
                        targetDirect hrename sourceItem targetItem
                        hsourceItem htargetItem
                      subst targetOccurrence
                      exact hoccurrence occurrence sourceDirect sourceItem
                        targetItem hsourceItem htargetItem)
                    hsourceItems htargetItems
                  simpa only [CompiledRegion.erase, CompilerCall.finish,
                    CompilerCall.castFullItems] using
                    regionIso_of_cast
                      (WireContext.length_extend sourceContext region)
                      (WireContext.length_extend targetContext
                        (equiv.regions region))
                      ambient (certifiedLocalWireEquiv equiv region)
                      sourceItems.erase targetItems.erase hitems)
  exact Classical.choice (allCalls
    (.nested region sourceContext rels sourceBinders)
    hwires htargetExact hbinders hsource htargetResult)
private noncomputable def compileRootCertifiedIso
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (hsourceWellFormed : source.WellFormed)
    (htargetWellFormed : target.WellFormed)
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hwires : CertifiedWireContextsAgree equiv
      (sourceAmbient ++ sourceLocal) (targetAmbient ++ targetLocal)
      (appendContextEquiv ambient localEquiv))
    (htargetExact : (targetAmbient ++ targetLocal).Exact target.root)
    {sourceBody : CompiledRegion source (.root sourceAmbient sourceLocal)}
    {targetBody : CompiledRegion target (.root targetAmbient targetLocal)}
    (hsource : compileRoot? source hsourceWellFormed sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot? target htargetWellFormed targetAmbient
      targetLocal = some targetBody) :
    {iso : RegionIso ambient [] sourceBody.erase targetBody.erase //
      iso.localEquivCast
          ((CompiledRegion.erase_localCount sourceBody).trans rfl)
          ((CompiledRegion.erase_localCount targetBody).trans rfl) =
        localEquiv} := by
  let sourceRoot := sourceAmbient ++ sourceLocal
  let targetRoot := targetAmbient ++ targetLocal
  let rootEquiv := appendContextEquiv ambient localEquiv
  have htargetExactMapped : targetRoot.Exact
      (equiv.regions source.root) := by
    simpa only [targetRoot, equiv.root_eq] using htargetExact
  have hbinders : CertifiedBinderContextsAgree equiv
      (BinderContext.empty : BinderContext source [])
      (BinderContext.empty : BinderContext target []) := by
    intro _
    rfl
  have hoccurrence : ∀
      (occurrence : LocalOccurrence source.regionCount source.nodeCount),
      (sourceDirect : occurrence ∈ localOccurrences source source.root) →
      (targetOccurrence :
        LocalOccurrence target.regionCount target.nodeCount) →
      (targetDirect : targetOccurrence ∈
        localOccurrences target (equiv.regions source.root)) →
      certifiedRenameOccurrence equiv occurrence = targetOccurrence →
      (sourceItem : CompiledItem source sourceRoot [] BinderContext.empty) →
      (targetItem : CompiledItem target targetRoot [] BinderContext.empty) →
      compileOccurrence? source hsourceWellFormed source.root sourceRoot
          BinderContext.empty occurrence sourceDirect = some sourceItem →
      compileOccurrence? target htargetWellFormed
          (equiv.regions source.root) targetRoot BinderContext.empty
          targetOccurrence targetDirect = some targetItem →
      ItemIso rootEquiv [] sourceItem.erase targetItem.erase := by
    intro occurrence sourceDirect targetOccurrence targetDirect hrename
      sourceItem targetItem hsourceItem htargetItem
    subst targetOccurrence
    cases occurrence with
    | node node =>
        exact compileNode?_certifiedEquivariant equiv htargetWellFormed hwires
          htargetExact.nodup hbinders node
          (by simpa [sourceRoot] using hsourceItem)
          (by
            simpa [targetRoot, certifiedRenameOccurrence] using htargetItem)
    | child child =>
        have hregionEq := equiv.regions_eq child
        cases hchild : source.regions child with
        | sheet =>
            rw [compileOccurrence?_child_sheet hsourceWellFormed source.root
              child sourceRoot BinderContext.empty sourceDirect hchild]
              at hsourceItem
            contradiction
        | cut parent =>
            have hparentSource :=
              (mem_localOccurrences_child source source.root child).mp
                sourceDirect
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
              htargetExactMapped.extend_child htargetWellFormed hparentTarget
            simp only [certifiedRenameOccurrence] at htargetItem
            rw [compileOccurrence?_child_cut hsourceWellFormed source.root
              child sourceRoot BinderContext.empty sourceDirect hchild]
              at hsourceItem
            rw [compileOccurrence?_child_cut htargetWellFormed
              (equiv.regions source.root) (equiv.regions child) targetRoot
              BinderContext.empty targetDirect hregionEq.symm] at htargetItem
            cases hsourceChild : compileRegion? source hsourceWellFormed child
                sourceRoot BinderContext.empty with
            | none => simp [hsourceChild] at hsourceItem
            | some sourceChild =>
                simp [hsourceChild] at hsourceItem
                subst sourceItem
                cases htargetChild : compileRegion? target htargetWellFormed
                    (equiv.regions child) targetRoot BinderContext.empty with
                | none => simp [htargetChild] at htargetItem
                | some targetChild =>
                    simp [htargetChild] at htargetItem
                    subst targetItem
                    exact .cut (compileRegion?_certifiedEquivariant equiv
                      hsourceWellFormed htargetWellFormed hwires hchildExact
                      hbinders hsourceChild htargetChild)
        | bubble parent arity =>
            have hparentSource :=
              (mem_localOccurrences_child source source.root child).mp
                sourceDirect
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
              htargetExactMapped.extend_child htargetWellFormed hparentTarget
            have hchildBinders := hbinders.push child arity
            simp only [certifiedRenameOccurrence] at htargetItem
            rw [compileOccurrence?_child_bubble hsourceWellFormed source.root
              child sourceRoot BinderContext.empty arity sourceDirect hchild]
              at hsourceItem
            rw [compileOccurrence?_child_bubble htargetWellFormed
              (equiv.regions source.root) (equiv.regions child) targetRoot
              BinderContext.empty arity targetDirect hregionEq.symm]
              at htargetItem
            cases hsourceChild : compileRegion? source hsourceWellFormed child
                sourceRoot (BinderContext.empty.push child arity) with
            | none => simp [hsourceChild] at hsourceItem
            | some sourceChild =>
                simp [hsourceChild] at hsourceItem
                subst sourceItem
                cases htargetChild : compileRegion? target htargetWellFormed
                    (equiv.regions child) targetRoot
                    (BinderContext.empty.push (equiv.regions child) arity) with
                | none => simp [htargetChild] at htargetItem
                | some targetChild =>
                    simp [htargetChild] at htargetItem
                    subst targetItem
                    exact .bubble (compileRegion?_certifiedEquivariant equiv
                      hsourceWellFormed htargetWellFormed hwires hchildExact
                      hchildBinders hsourceChild htargetChild)
  rw [compileRoot?_eq_compileItems? hsourceWellFormed] at hsource
  rw [compileRoot?_eq_compileItems? htargetWellFormed] at htargetResult
  cases hsourceItems : compileItems? source hsourceWellFormed source.root
      sourceRoot BinderContext.empty (localOccurrences source source.root)
      (fun _ member => member) with
  | none => simp [sourceRoot, hsourceItems] at hsource
  | some sourceItems =>
      simp [sourceRoot, hsourceItems] at hsource
      subst sourceBody
      cases htargetItems : compileItems? target htargetWellFormed target.root
          targetRoot BinderContext.empty (localOccurrences target target.root)
          (fun _ member => member) with
      | none => simp [targetRoot, htargetItems] at htargetResult
      | some targetItems =>
          simp [targetRoot, htargetItems] at htargetResult
          subst targetBody
          have htargetItemsMapped : compileItems? target htargetWellFormed
              (equiv.regions source.root) targetRoot BinderContext.empty
              (localOccurrences target (equiv.regions source.root))
              (fun _ member => member) = some targetItems := by
            simpa only [equiv.root_eq] using htargetItems
          have hitems : ItemSeqIso rootEquiv [] sourceItems.erase
              targetItems.erase :=
            compileItems?_certifiedEquivariant equiv hsourceWellFormed
              htargetWellFormed hoccurrence hsourceItems htargetItemsMapped
          have sourceWireEq : sourceRoot.length =
              sourceAmbient.length + sourceLocal.length :=
            List.length_append
          have targetWireEq : targetRoot.length =
              targetAmbient.length + targetLocal.length :=
            List.length_append
          let result : RegionIso ambient []
              (@CompiledRegion.mk source (.root sourceAmbient sourceLocal)
                sourceItems).erase
              (@CompiledRegion.mk target (.root targetAmbient targetLocal)
                targetItems).erase := by
            simpa only [CompiledRegion.erase, CompilerCall.finish,
              CompilerCall.castFullItems, sourceRoot, targetRoot,
              rootEquiv] using
              regionIso_of_cast sourceWireEq targetWireEq ambient localEquiv
                sourceItems.erase targetItems.erase hitems
          refine ⟨result, ?_⟩
          change result.localEquiv = localEquiv
          exact regionIso_of_cast_localEquiv sourceWireEq targetWireEq ambient
            localEquiv sourceItems.erase targetItems.erase hitems
noncomputable def compileRoot?_certifiedEquivariant
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (hsource : source.WellFormed)
    (htarget : target.WellFormed)
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hwires : CertifiedWireContextsAgree equiv
      (sourceAmbient ++ sourceLocal) (targetAmbient ++ targetLocal)
      (appendContextEquiv ambient localEquiv))
    (htargetExact : (targetAmbient ++ targetLocal).Exact target.root)
    {sourceBody : CompiledRegion source (.root sourceAmbient sourceLocal)}
    {targetBody : CompiledRegion target (.root targetAmbient targetLocal)}
    (hsourceResult : compileRoot? source hsource sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot? target htarget targetAmbient targetLocal =
      some targetBody) :
    RegionIso ambient [] sourceBody.erase targetBody.erase :=
  (compileRootCertifiedIso equiv hsource htarget hwires htargetExact
    hsourceResult
    htargetResult).val

theorem compileRoot?_certifiedEquivariant_localEquivCast
    {source target : Diagram}
    (equiv : OccurrenceEquiv source target)
    (hsource : source.WellFormed)
    (htarget : target.WellFormed)
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hwires : CertifiedWireContextsAgree equiv
      (sourceAmbient ++ sourceLocal) (targetAmbient ++ targetLocal)
      (appendContextEquiv ambient localEquiv))
    (htargetExact : (targetAmbient ++ targetLocal).Exact target.root)
    {sourceBody : CompiledRegion source (.root sourceAmbient sourceLocal)}
    {targetBody : CompiledRegion target (.root targetAmbient targetLocal)}
    (hsourceResult : compileRoot? source hsource sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot? target htarget targetAmbient targetLocal =
      some targetBody)
    (sourceLocalEq : sourceBody.erase.localCount = sourceLocal.length)
    (targetLocalEq : targetBody.erase.localCount = targetLocal.length) :
    (compileRoot?_certifiedEquivariant equiv hsource htarget hwires htargetExact
      hsourceResult htargetResult).localEquivCast sourceLocalEq targetLocalEq =
        localEquiv := by
  let result := compileRootCertifiedIso equiv hsource htarget hwires
    htargetExact hsourceResult htargetResult
  have sourceProofEq : sourceLocalEq =
      (CompiledRegion.erase_localCount sourceBody).trans rfl :=
    Subsingleton.elim _ _
  have targetProofEq : targetLocalEq =
      (CompiledRegion.erase_localCount targetBody).trans rfl :=
    Subsingleton.elim _ _
  rw [sourceProofEq, targetProofEq]
  exact result.property

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
  exact (CompiledRegion.erase_localCount body).trans
    (Elaboration.compileRoot?_localCount
      checked.property.diagram_well_formed compiled)

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
  have hambient : Elaboration.WireContextsAgree iso
      ([] : Elaboration.WireContext source)
      ([] : Elaboration.WireContext target) (.refl (Fin 0)) := by
    intro index
    exact Fin.elim0 index
  have hlocalRoot : ∃ localEquiv : FiniteEquiv
      (Fin (Elaboration.exactScopeWires source source.root).length)
      (Fin (Elaboration.exactScopeWires target target.root).length),
      Elaboration.WireContextsAgree iso
        (Elaboration.exactScopeWires source source.root)
        (Elaboration.exactScopeWires target target.root) localEquiv := by
    rw [← iso.root_eq]
    exact ⟨Elaboration.localWireEquiv iso source.root,
      Elaboration.localWireEquiv_spec iso source.root⟩
  obtain ⟨localEquiv, hlocal⟩ := hlocalRoot
  have hwires := Elaboration.appendContextsAgree hambient hlocal
  have htargetExact : Elaboration.WireContext.Exact
      (([] : Elaboration.WireContext target) ++
        Elaboration.exactScopeWires target
          target.root) target.root := by
    exact Elaboration.closedRootWires_exact htarget
  let occurrenceEquiv := OccurrenceEquiv.ofConcreteIso iso
  have hwiresCertified : CertifiedWireContextsAgree occurrenceEquiv
      (([] : Elaboration.WireContext source) ++
        Elaboration.exactScopeWires source source.root)
      (([] : Elaboration.WireContext target) ++
        Elaboration.exactScopeWires target target.root)
      (Elaboration.appendContextEquiv (.refl (Fin 0)) localEquiv) := hwires
  have hbody : RegionIso  (.refl (Fin 0)) [] sourceBody.erase targetBody.erase :=
    compileRoot?_certifiedEquivariant occurrenceEquiv hsource htarget
      hwiresCertified htargetExact hsourceKernel htargetKernel
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
  let occurrenceEquiv := OccurrenceEquiv.ofConcreteIso iso.diagram
  have hwiresCertified : CertifiedWireContextsAgree occurrenceEquiv
      (source.exposedWires ++ source.hiddenWires)
      (target.exposedWires ++ target.hiddenWires)
      (Elaboration.appendContextEquiv iso.exposedWiresEquiv
        iso.hiddenWiresEquiv) := hwires
  have hbody : RegionIso  iso.exposedWiresEquiv []
      (source.elaborate hsource).body (target.elaborate htarget).body := by
    have hsourceKernel : compileRoot? source.diagram
        hsource.diagram_well_formed source.exposedWires source.hiddenWires =
          some (CheckedOpen.compilation ⟨source, hsource⟩) :=
      CheckedOpen.compilation_computation ⟨source, hsource⟩
    have htargetKernel : compileRoot? target.diagram
        htarget.diagram_well_formed target.exposedWires target.hiddenWires =
          some (CheckedOpen.compilation ⟨target, htarget⟩) :=
      CheckedOpen.compilation_computation ⟨target, htarget⟩
    simpa [OpenDiagram.elaborate, CheckedOpen.elaborate] using
      compileRoot?_certifiedEquivariant occurrenceEquiv
        hsource.diagram_well_formed htarget.diagram_well_formed
        hwiresCertified htargetExact
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
  rw [openDiagramIso_ofArityEq_localEquivCast]
  · apply compileRoot?_certifiedEquivariant_localEquivCast
  · exact target.elaborate_body_localCount htarget

end OpenIso

end VisualProof.Concrete
