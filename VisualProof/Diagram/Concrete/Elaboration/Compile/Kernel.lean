import VisualProof.Diagram.Concrete.Elaboration.Context
import VisualProof.Diagram.Concrete.Open
import VisualProof.Diagram.Concrete.Examples
import VisualProof.Diagram.Concrete.OpenIsomorphism
import VisualProof.Diagram.Concrete.Occurrence
import VisualProof.Diagram.OpenIsomorphism
import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

def renameOccurrence {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) :
    LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount
  | .node node => .node (iso.nodes node)
  | .child region => .child (iso.regions region)

private def occurrenceEquiv {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) :
    FiniteEquiv
      (LocalOccurrence source.regionCount source.nodeCount)
      (LocalOccurrence target.regionCount target.nodeCount) where
  toFun := renameOccurrence iso
  invFun := renameOccurrence iso.symm
  left_inv := by
    intro occurrence
    cases occurrence with
    | node node => exact congrArg LocalOccurrence.node (iso.nodes.left_inv node)
    | child region => exact congrArg LocalOccurrence.child (iso.regions.left_inv region)
  right_inv := by
    intro occurrence
    cases occurrence with
    | node node => exact congrArg LocalOccurrence.node (iso.nodes.right_inv node)
    | child region => exact congrArg LocalOccurrence.child (iso.regions.right_inv region)

private theorem exactScopeWires_mem_iff {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount)
    (wire : Fin source.wireCount) :
    iso.wires wire ∈ exactScopeWires target (iso.regions region) ↔
      wire ∈ exactScopeWires source region := by
  simp only [mem_exactScopeWires]
  rw [<- iso.wire_scope_eq wire]
  constructor
  · intro h
    have := congrArg iso.regions.invFun h
    simpa only [iso.regions.left_inv] using this
  · exact congrArg iso.regions

def localWireEquiv {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (exactScopeWires source region).length)
      (Fin (exactScopeWires target (iso.regions region)).length) :=
  FiniteEquiv.restrictLists iso.wires _ _
    (exactScopeWires_nodup source region)
    (exactScopeWires_nodup target (iso.regions region))
    (exactScopeWires_mem_iff iso region)

theorem localWireEquiv_spec {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount)
    (index : Fin (exactScopeWires source region).length) :
    (exactScopeWires target (iso.regions region)).get
        (localWireEquiv iso region index) =
      iso.wires ((exactScopeWires source region).get index) :=
  FiniteEquiv.restrictLists_spec iso.wires _ _ _ _ _ index

private theorem localOccurrences_mem_iff {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount)
    (occurrence : LocalOccurrence source.regionCount source.nodeCount) :
    renameOccurrence iso occurrence ∈
        localOccurrences target (iso.regions region) ↔
      occurrence ∈ localOccurrences source region := by
  cases occurrence with
  | node node =>
      simp only [renameOccurrence, mem_localOccurrences_node]
      rw [<- iso.nodes_eq node, CNode.region_rename]
      constructor
      · intro h
        have := congrArg iso.regions.invFun h
        simpa only [iso.regions.left_inv] using this
      · exact congrArg iso.regions
  | child child =>
      simp only [renameOccurrence, mem_localOccurrences_child]
      rw [<- iso.regions_eq child, CRegion.parent?_rename]
      cases hparent : (source.regions child).parent? with
      | none => simp
      | some parent =>
          simp only [Option.map_some, Option.some.injEq]
          constructor
          · intro h
            have := congrArg iso.regions.invFun h
            simpa only [iso.regions.left_inv] using this
          · exact congrArg iso.regions

def localOccurrenceEquiv {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (localOccurrences source region).length)
      (Fin (localOccurrences target (iso.regions region)).length) :=
  FiniteEquiv.restrictLists (occurrenceEquiv iso) _ _
    (localOccurrences_nodup source region)
    (localOccurrences_nodup target (iso.regions region))
    (localOccurrences_mem_iff iso region)

theorem localOccurrenceEquiv_spec {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount)
    (index : Fin (localOccurrences source region).length) :
    (localOccurrences target (iso.regions region)).get
        (localOccurrenceEquiv iso region index) =
      renameOccurrence iso ((localOccurrences source region).get index) :=
  FiniteEquiv.restrictLists_spec (occurrenceEquiv iso) _ _ _ _ _ index

def WireContextsAgree {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)) : Prop :=
  forall index, targetContext.get (ambient index) =
    iso.wires (sourceContext.get index)

/-- Transport an exact lexical wire context through a concrete isomorphism. -/
theorem WireContext.Exact.mapIso
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    {context : WireContext source} {region : Fin source.regionCount}
    (exact : context.Exact region) :
    WireContext.Exact (context.map iso.wires) (iso.regions region) := by
  constructor
  · exact exact.nodup.map iso.wires (fun _ _ distinct equality =>
      distinct (iso.wires.injective equality))
  · intro targetWire
    rw [List.mem_map]
    constructor
    · rintro ⟨sourceWire, sourceMember, rfl⟩
      rw [exact.mem_iff] at sourceMember
      simpa only [iso.wire_scope_eq] using iso.encloses_transport sourceMember
    · intro targetVisible
      let sourceWire := iso.symm.wires targetWire
      refine ⟨sourceWire, (exact.mem_iff sourceWire).2 ?_,
        iso.wires.right_inv targetWire⟩
      have transported := iso.symm.encloses_transport targetVisible
      rw [iso.symm.wire_scope_eq targetWire] at transported
      rw [show iso.symm.regions (iso.regions region) = region by
        exact iso.regions.left_inv region] at transported
      exact transported

def BinderContextsAgree {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (sourceContext : BinderContext source rels)
    (targetContext : BinderContext target rels) : Prop :=
  forall binder, targetContext (iso.regions binder) = sourceContext binder

/-- Binder coverage is invariant under a concrete isomorphism when lookup
contexts agree along the region equivalence. -/
theorem BinderContext.Covers.mapIso
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    {sourceContext : BinderContext source rels}
    {targetContext : BinderContext target rels}
    (agrees : BinderContextsAgree iso sourceContext targetContext)
    {region : Fin source.regionCount}
    (covers : sourceContext.Covers region) :
    targetContext.Covers (iso.regions region) := by
  intro targetBinder targetParent arity targetBubble targetEncloses
  let sourceBinder := iso.symm.regions targetBinder
  let sourceParent := iso.symm.regions targetParent
  have sourceBubble : source.regions sourceBinder =
      .bubble sourceParent arity := by
    have renamed := iso.symm.regions_eq targetBinder
    rw [targetBubble] at renamed
    simpa only [sourceBinder, sourceParent, CRegion.rename] using renamed.symm
  have sourceEncloses : source.Encloses sourceBinder region := by
    have transported := iso.symm.encloses_transport targetEncloses
    rw [show iso.symm.regions (iso.regions region) = region by
      exact iso.regions.left_inv region] at transported
    exact transported
  obtain ⟨relation, sourceLookup⟩ :=
    covers sourceBinder sourceParent arity sourceBubble sourceEncloses
  refine ⟨relation, ?_⟩
  have lookup := agrees sourceBinder
  rw [show iso.regions sourceBinder = targetBinder by
    exact iso.regions.right_inv targetBinder] at lookup
  exact lookup.trans sourceLookup

/-- Exact binder enumeration transported through a concrete isomorphism. -/
def BinderContext.Enumeration.mapIso
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    {sourceContext : BinderContext source rels}
    {targetContext : BinderContext target rels}
    (agrees : BinderContextsAgree iso sourceContext targetContext)
    {region : Fin source.regionCount}
    (enumeration : BinderContext.Enumeration source sourceContext region) :
    BinderContext.Enumeration target targetContext (iso.regions region) where
  binder := fun index => iso.regions (enumeration.binder index)
  binder_injective := fun _ _ equality =>
    enumeration.binder_injective (iso.regions.injective equality)
  bubble := by
    intro index
    obtain ⟨parent, sourceBubble⟩ := enumeration.bubble index
    refine ⟨iso.regions parent, ?_⟩
    rw [← iso.regions_eq (enumeration.binder index), sourceBubble]
    rfl
  encloses := fun index => iso.encloses_transport (enumeration.encloses index)
  lookup := fun index => agrees (enumeration.binder index) |>.trans
    (enumeration.lookup index)
  lookup_owner := by
    intro candidate arity relation targetLookup
    let sourceCandidate := iso.symm.regions candidate
    have agreement := agrees sourceCandidate
    rw [show iso.regions sourceCandidate = candidate by
      exact iso.regions.right_inv candidate] at agreement
    have sourceOwner := enumeration.lookup_owner relation
      (agreement.symm.trans targetLookup)
    rw [sourceOwner]
    exact iso.regions.right_inv candidate

theorem BinderContextsAgree.push {source target : ConcreteDiagram}
    {iso : ConcreteIso source target}
    {sourceContext : BinderContext source rels}
    {targetContext : BinderContext target rels}
    (hagrees : BinderContextsAgree iso sourceContext targetContext)
    (binder : Fin source.regionCount) (arity : Nat) :
    BinderContextsAgree iso (sourceContext.push binder arity)
      (targetContext.push (iso.regions binder) arity) := by
  intro candidate
  by_cases heq : candidate = binder
  · subst candidate
    simp
  · have hmapped : iso.regions candidate ≠ iso.regions binder :=
      fun h => heq (by
        have := congrArg iso.regions.invFun h
        simpa only [iso.regions.left_inv] using this)
    rw [BinderContext.push_other _ arity hmapped,
      BinderContext.push_other _ arity heq, hagrees]

def castFinEquiv {source target source' target' : Nat}
    (sourceEq : source = source') (targetEq : target = target')
    (equivalence : FiniteEquiv (Fin source') (Fin target')) :
    FiniteEquiv (Fin source) (Fin target) where
  toFun index := Fin.cast targetEq.symm (equivalence (Fin.cast sourceEq index))
  invFun index := Fin.cast sourceEq.symm
    (equivalence.symm (Fin.cast targetEq index))
  left_inv := by
    intro index
    apply Fin.ext
    change (equivalence.symm (equivalence (Fin.cast sourceEq index))).val =
      index.val
    exact (congrArg Fin.val (equivalence.left_inv (Fin.cast sourceEq index))).trans
      rfl
  right_inv := by
    intro index
    apply Fin.ext
    change (equivalence (equivalence.symm (Fin.cast targetEq index))).val =
      index.val
    exact (congrArg Fin.val (equivalence.right_inv (Fin.cast targetEq index))).trans
      rfl

@[simp] private theorem castFinEquiv_rfl
    (equivalence : FiniteEquiv (Fin source) (Fin target)) :
    castFinEquiv rfl rfl equivalence = equivalence := by
  apply FiniteEquiv.ext
  intro index
  rfl

def extendedContextEquiv {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length))
    (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (sourceContext.extend region).length)
      (Fin (targetContext.extend (iso.regions region)).length) :=
  castFinEquiv (WireContext.length_extend sourceContext region)
    (WireContext.length_extend targetContext (iso.regions region))
    (extendWireEquiv ambient (localWireEquiv iso region))

theorem get_append_castAdd (initial : List alpha) (suffix : List alpha)
    (index : Fin initial.length) :
    (initial ++ suffix).get
        (Fin.cast (by simp) (Fin.castAdd suffix.length index)) =
      initial.get index := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left index.isLt

theorem get_append_natAdd (initial : List alpha) (suffix : List alpha)
    (index : Fin suffix.length) :
    (initial ++ suffix).get
        (Fin.cast (by simp) (Fin.natAdd initial.length index)) =
      suffix.get index := by
  simp [List.get_eq_getElem]

def appendContextEquiv
    {sourceWire targetWire : Type}
    {sourceAmbient sourceLocal : List sourceWire}
    {targetAmbient targetLocal : List targetWire}
    (ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length))
    (localEquiv : FiniteEquiv (Fin sourceLocal.length) (Fin targetLocal.length)) :
    FiniteEquiv (Fin (sourceAmbient ++ sourceLocal).length)
      (Fin (targetAmbient ++ targetLocal).length) :=
  castFinEquiv (by simp) (by simp)
    (extendWireEquiv ambient localEquiv)

theorem appendContextsAgree {source target : ConcreteDiagram}
    {iso : ConcreteIso source target}
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length) (Fin targetLocal.length)}
    (hambient : WireContextsAgree iso sourceAmbient targetAmbient ambient)
    (hlocal : WireContextsAgree iso sourceLocal targetLocal localEquiv) :
    WireContextsAgree iso (sourceAmbient ++ sourceLocal)
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
      _ = iso.wires (sourceAmbient.get outer) := hambient outer
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
      _ = iso.wires (sourceLocal.get localIndex) := hlocal localIndex

private theorem appendWireContextsAgree {source target : ConcreteDiagram}
    {iso : ConcreteIso source target}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hagrees : WireContextsAgree iso sourceContext targetContext ambient)
    (region : Fin source.regionCount) :
    forall index : Fin
        (sourceContext.length + (exactScopeWires source region).length),
      (targetContext ++ exactScopeWires target (iso.regions region)).get
          (Fin.cast (by simp)
            (extendWireEquiv ambient (localWireEquiv iso region) index)) =
        iso.wires
          ((sourceContext ++ exactScopeWires source region).get
            (Fin.cast (by simp) index)) := by
  intro index
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) index
  · rw [extendWireEquiv_outer, get_append_castAdd, get_append_castAdd]
    exact hagrees outer
  · rw [extendWireEquiv_local, get_append_natAdd, get_append_natAdd]
    exact localWireEquiv_spec iso region localIndex

theorem WireContextsAgree.extend {source target : ConcreteDiagram}
    {iso : ConcreteIso source target}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hagrees : WireContextsAgree iso sourceContext targetContext ambient)
    (region : Fin source.regionCount) :
    WireContextsAgree iso
      (sourceContext.extend region)
      (targetContext.extend (iso.regions region))
      (extendedContextEquiv iso sourceContext targetContext ambient region) := by
  intro index
  let sourceIndex : Fin
      (sourceContext.length + (exactScopeWires source region).length) :=
    Fin.cast (WireContext.length_extend sourceContext region) index
  have h := appendWireContextsAgree hagrees region sourceIndex
  change (targetContext ++ exactScopeWires target (iso.regions region)).get
      (Fin.cast (WireContext.length_extend targetContext (iso.regions region)).symm
        (extendWireEquiv ambient (localWireEquiv iso region) sourceIndex)) =
    iso.wires ((sourceContext ++ exactScopeWires source region).get index)
  have hsource : Fin.cast (by simp) sourceIndex = index := by
    apply Fin.ext
    rfl
  calc
    _ = iso.wires ((sourceContext ++ exactScopeWires source region).get
          (Fin.cast (by simp) sourceIndex)) := h
    _ = _ := congrArg iso.wires (congrArg
      (sourceContext ++ exactScopeWires source region).get hsource)

private theorem resolvePort?_equivariant {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hagrees : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    (node : Fin source.nodeCount) (port : CPort)
    {sourceIndex : Fin sourceContext.length}
    {targetIndex : Fin targetContext.length}
    (hsource : resolvePort? source sourceContext node port = some sourceIndex)
    (htargetResult : resolvePort? target targetContext (iso.nodes node) port =
      some targetIndex) :
    ambient sourceIndex = targetIndex := by
  obtain ⟨sourceWire, hsourceOccurs, hsourceValue⟩ := resolvePort?_sound hsource
  obtain ⟨targetWire, htargetOccurs, htargetValue⟩ :=
    resolvePort?_sound htargetResult
  have hmappedOccurs : target.EndpointOccurs (iso.wires sourceWire)
      ⟨iso.nodes node, port⟩ := by
    simpa only [CEndpoint.rename] using
      iso.endpointOccurs_transport hsourceOccurs
  have hwire : iso.wires sourceWire = targetWire :=
    endpoint_wire_unique htarget.wire_endpoints_are_disjoint
      hmappedOccurs htargetOccurs
  have hvalues : targetContext.get (ambient sourceIndex) =
      targetContext.get targetIndex := by
    rw [hagrees]
    have hsourceGet : sourceContext.get sourceIndex = sourceWire := by
      simpa only [List.get_eq_getElem] using hsourceValue
    have htargetGet : targetContext.get targetIndex = targetWire := by
      simpa only [List.get_eq_getElem] using htargetValue
    rw [hsourceGet, hwire, htargetGet]
  apply Fin.ext
  exact (List.getElem_inj htargetNodup).mp (by
    simpa only [List.get_eq_getElem] using hvalues)

private theorem resolvePorts?_equivariant {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hagrees : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    (node : Fin source.nodeCount) (arity : Nat) (port : Fin arity → CPort)
    {sourceResult : Fin arity → Fin sourceContext.length}
    {targetResult : Fin arity → Fin targetContext.length}
    (hsource : resolvePorts? source sourceContext node arity port =
      some sourceResult)
    (htargetResult : resolvePorts? target targetContext (iso.nodes node) arity port =
      some targetResult) :
    ambient.toFun ∘ sourceResult = targetResult := by
  funext index
  exact resolvePort?_equivariant iso htarget hagrees htargetNodup node (port index)
    (sequenceFin_sound hsource index) (sequenceFin_sound htargetResult index)

theorem sequenceFin_map
    (map : α → β) (values : Fin arity → Option α) :
    sequenceFin (fun index => (values index).map map) =
      (sequenceFin values).map (fun result index => map (result index)) := by
  induction arity with
  | zero =>
      simp only [sequenceFin, Option.map_some]
      apply congrArg some
      funext index
      exact Fin.elim0 index
  | succ arity ih =>
      simp only [sequenceFin]
      cases hhead : values 0 with
      | none => simp [hhead]
      | some head =>
          cases htail : sequenceFin (fun index => values index.succ) with
          | none =>
              have hmappedTail := ih (fun index => values index.succ)
              rw [htail] at hmappedTail
              simp [hhead, hmappedTail]
          | some tail =>
              have hmappedTail := ih (fun index => values index.succ)
              rw [htail] at hmappedTail
              simp [hhead, hmappedTail]
              funext index
              refine Fin.cases ?_ (fun tailIndex => ?_) index <;> rfl

theorem resolvePorts?_map
    {source target : ConcreteDiagram}
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceNode : Fin source.nodeCount)
    (targetNode : Fin target.nodeCount)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (arity : Nat) (port : Fin arity → CPort)
    (hport : ∀ requested,
      resolvePort? target targetContext targetNode requested =
        (resolvePort? source sourceContext sourceNode requested).map wireMap) :
    resolvePorts? target targetContext targetNode arity port =
      (resolvePorts? source sourceContext sourceNode arity port).map
        (fun result => wireMap ∘ result) := by
  unfold resolvePorts?
  rw [show (fun index => resolvePort? target targetContext targetNode
      (port index)) =
      (fun index => (resolvePort? source sourceContext sourceNode
        (port index)).map wireMap) by
    funext index
    exact hport (port index)]
  rw [sequenceFin_map]
  congr 2

/-- Transport lexical lookup through an exact index map for one concrete wire.
The map may embed the source context into a larger target context; the
membership equivalence rules out an accidental second authority for the
mapped wire. -/
theorem WireContext.lookup?_map
    {source target : ConcreteDiagram}
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (concreteWireMap : Fin source.wireCount → Fin target.wireCount)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (targetNodup : targetContext.Nodup)
    (hget : ∀ index,
      targetContext.get (indexMap index) =
        concreteWireMap (sourceContext.get index))
    (hmem : ∀ wire,
      concreteWireMap wire ∈ targetContext ↔ wire ∈ sourceContext)
    (wire : Fin source.wireCount) :
    targetContext.lookup? (concreteWireMap wire) =
      (sourceContext.lookup? wire).map indexMap := by
  cases hsource : sourceContext.lookup? wire with
  | none =>
      have hnotSource : wire ∉ sourceContext := by
        intro hmember
        obtain ⟨index, hindex⟩ := sourceContext.lookup?_complete hmember
        rw [hsource] at hindex
        contradiction
      have hnotTarget : concreteWireMap wire ∉ targetContext :=
        fun htarget => hnotSource ((hmem wire).1 htarget)
      cases htarget : targetContext.lookup? (concreteWireMap wire) with
      | none => simp [hsource, htarget]
      | some index =>
          have hfound := WireContext.lookup?_sound htarget
          have hindexMember : targetContext.get index ∈ targetContext :=
            List.get_mem targetContext index
          have hvalue : targetContext.get index = concreteWireMap wire := by
            simpa only [List.get_eq_getElem] using hfound
          rw [hvalue] at hindexMember
          exact False.elim (hnotTarget hindexMember)
  | some sourceIndex =>
      have hsourceGet : sourceContext.get sourceIndex = wire := by
        simpa only [List.get_eq_getElem] using WireContext.lookup?_sound hsource
      have htargetMember : concreteWireMap wire ∈ targetContext :=
        (hmem wire).2 (by
          rw [← hsourceGet]
          exact List.get_mem sourceContext sourceIndex)
      obtain ⟨targetIndex, htarget⟩ :=
        targetContext.lookup?_complete htargetMember
      have htargetGet : targetContext.get targetIndex = concreteWireMap wire := by
        simpa only [List.get_eq_getElem] using WireContext.lookup?_sound htarget
      have hindices : targetIndex = indexMap sourceIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetNodup).mp (by
          simpa only [List.get_eq_getElem] using
            htargetGet.trans ((hget sourceIndex).trans
              (congrArg concreteWireMap hsourceGet)).symm)
      simp only [Option.map_some]
      rw [htarget, hindices]

/-- Transport endpoint ownership through an exact occurrence correspondence.
This is independent of storage order and therefore remains valid when splice
adds endpoints to other wires. -/
theorem endpointOwner?_map
    {source target : ConcreteDiagram}
    (sourceNode : Fin source.nodeCount)
    (targetNode : Fin target.nodeCount)
    (concreteWireMap : Fin source.wireCount → Fin target.wireCount)
    (port : CPort)
    (hforward : ∀ wire,
      source.EndpointOccurs wire ⟨sourceNode, port⟩ →
        target.EndpointOccurs (concreteWireMap wire) ⟨targetNode, port⟩)
    (hbackward : ∀ targetWire,
      target.EndpointOccurs targetWire ⟨targetNode, port⟩ →
        ∃ sourceWire,
          concreteWireMap sourceWire = targetWire ∧
            source.EndpointOccurs sourceWire ⟨sourceNode, port⟩)
    (targetDisjoint : target.WireEndpointsAreDisjoint) :
    endpointOwner? target ⟨targetNode, port⟩ =
      (endpointOwner? source ⟨sourceNode, port⟩).map concreteWireMap := by
  cases hsource : endpointOwner? source ⟨sourceNode, port⟩ with
  | none =>
      cases htarget : endpointOwner? target ⟨targetNode, port⟩ with
      | none => simp
      | some targetWire =>
          obtain ⟨sourceWire, _, hsourceOccurs⟩ :=
            hbackward targetWire (endpointOwner?_sound htarget)
          obtain ⟨owner, howner⟩ := endpointOwner?_complete hsourceOccurs
          rw [hsource] at howner
          contradiction
  | some sourceWire =>
      have hmappedOccurs := hforward sourceWire
        (endpointOwner?_sound hsource)
      obtain ⟨targetWire, htarget⟩ := endpointOwner?_complete hmappedOccurs
      have heq : targetWire = concreteWireMap sourceWire :=
        endpoint_wire_unique targetDisjoint
          (endpointOwner?_sound htarget) hmappedOccurs
      simp only [Option.map_some]
      rw [htarget, heq]

/-- Port resolution is the composition of transported endpoint ownership and
transported lexical lookup. -/
theorem resolvePort?_map_of_occurrence
    {source target : ConcreteDiagram}
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceNode : Fin source.nodeCount)
    (targetNode : Fin target.nodeCount)
    (concreteWireMap : Fin source.wireCount → Fin target.wireCount)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (targetNodup : targetContext.Nodup)
    (hget : ∀ index,
      targetContext.get (indexMap index) =
        concreteWireMap (sourceContext.get index))
    (hmem : ∀ wire,
      concreteWireMap wire ∈ targetContext ↔ wire ∈ sourceContext)
    (hforward : ∀ wire port,
      source.EndpointOccurs wire ⟨sourceNode, port⟩ →
        target.EndpointOccurs (concreteWireMap wire) ⟨targetNode, port⟩)
    (hbackward : ∀ targetWire port,
      target.EndpointOccurs targetWire ⟨targetNode, port⟩ →
        ∃ sourceWire,
          concreteWireMap sourceWire = targetWire ∧
            source.EndpointOccurs sourceWire ⟨sourceNode, port⟩)
    (targetDisjoint : target.WireEndpointsAreDisjoint)
    (port : CPort) :
    resolvePort? target targetContext targetNode port =
      (resolvePort? source sourceContext sourceNode port).map indexMap := by
  unfold resolvePort?
  rw [endpointOwner?_map sourceNode targetNode concreteWireMap port
    (fun wire => hforward wire port) (fun wire => hbackward wire port)
    targetDisjoint]
  cases howner : endpointOwner? source ⟨sourceNode, port⟩ with
  | none => simp
  | some wire =>
      simp only [Option.map_some, Option.bind_some]
      exact WireContext.lookup?_map sourceContext targetContext concreteWireMap
        indexMap targetNodup hget hmem wire

/-- Compositional node kernel of the sole concrete elaborator.  Public so graph
surgeries can prove that they commute with elaboration. -/
def compileNode? (signature : List Nat) (d : ConcreteDiagram)
    (context : WireContext d) (binders : BinderContext d rels)
    (node : Fin d.nodeCount) : Option (Item signature context.length rels) :=
  match d.nodes node with
  | .term _ freePorts term => do
      let output <- resolvePort? d context node .output
      let free <- resolvePorts? d context node freePorts (fun index => .free index)
      pure (.equation output (term.mapFree free))
  | .atom _ binder => do
      let relation <- binders binder
      let arguments <- resolvePorts? d context node relation.1
      pure (.atom relation.2 arguments)
  | .named _ definition arity => do
      let relation <- namedRel? signature definition arity
      let arguments <- resolvePorts? d context node arity
      pure (.named relation arguments)

/-- Transport one node compilation through an embedding of its concrete
region/binder identities and a (not necessarily surjective) embedding of the
visible wire context.  Graph-surgery proofs discharge the concrete lookup
hypotheses; this theorem owns the intrinsic renaming calculation. -/
theorem compileNode?_map
    {source target : ConcreteDiagram}
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (sourceNode : Fin source.nodeCount)
    (targetNode : Fin target.nodeCount)
    (regionMap : Fin source.regionCount → Fin target.regionCount)
    (binderMap : Fin source.regionCount → Fin target.regionCount)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (hnode : target.nodes targetNode =
      match source.nodes sourceNode with
      | .term region freePorts term =>
          .term (regionMap region) freePorts term
      | .atom region binder =>
          .atom (regionMap region) (binderMap binder)
      | .named region definition arity =>
          .named (regionMap region) definition arity)
    (hports : ∀ port,
      resolvePort? target targetContext targetNode port =
        (resolvePort? source sourceContext sourceNode port).map wireMap)
    (hbinders : ∀ region binder,
      source.nodes sourceNode = .atom region binder →
        targetBinders (binderMap binder) =
          (sourceBinders binder).map fun relation =>
            ⟨relation.1, relationMap relation.2⟩) :
    compileNode? signature target targetContext targetBinders targetNode =
      (compileNode? signature source sourceContext sourceBinders sourceNode).map
        (fun item =>
          (item.renameWires wireMap).renameRelations relationMap) := by
  cases hsourceNode : source.nodes sourceNode with
  | term region freePorts term =>
      simp only [compileNode?, hsourceNode, hnode]
      rw [hports .output]
      have hfree := resolvePorts?_map sourceContext targetContext sourceNode
        targetNode wireMap freePorts (fun index => .free index) hports
      rw [hfree]
      cases houtput : resolvePort? source sourceContext sourceNode .output <;>
        simp [houtput]
      cases hfreeSource : resolvePorts? source sourceContext sourceNode
          freePorts (fun index => .free index) <;>
        simp [hfreeSource, Item.renameWires, Item.renameRelations,
          Lambda.Term.mapFree_comp, Function.comp_def]
  | atom region binder =>
      simp only [compileNode?, hsourceNode, hnode]
      rw [hbinders region binder hsourceNode]
      cases hrelation : sourceBinders binder with
      | none => simp [hrelation]
      | some relation =>
          cases relation with
          | mk arity relation =>
              simp only [Option.map_some]
              dsimp
              have harguments := resolvePorts?_map sourceContext targetContext
                sourceNode targetNode wireMap arity
                (fun index => .arg index) hports
              rw [harguments]
              cases hsourceArguments : resolvePorts? source sourceContext
                  sourceNode arity (fun index => .arg index) <;>
                simp [hrelation, hsourceArguments, Item.renameWires,
                  Item.renameRelations, Function.comp_def]
  | named region definition arity =>
      simp only [compileNode?, hsourceNode, hnode]
      have harguments := resolvePorts?_map sourceContext targetContext
        sourceNode targetNode wireMap arity (fun index => .arg index) hports
      rw [harguments]
      cases hrelation : namedRel? signature definition arity <;>
        simp [hrelation]
      cases hsourceArguments : resolvePorts? source sourceContext sourceNode
          arity (fun index => .arg index) <;>
        simp [hsourceArguments, Item.renameWires, Item.renameRelations,
          Function.comp_def]

theorem namedRel?_appendRight
    {signature suffix : List Nat} {definition arity : Nat}
    {relation : NamedRel signature arity}
    (hrelation : namedRel? signature definition arity = some relation) :
    namedRel? (signature ++ suffix) definition arity =
      some ((NamedRenaming.appendRight signature suffix).named relation) := by
  obtain ⟨hindex, hlookup⟩ := namedRel?_sound hrelation
  obtain ⟨hdefinition, hvalue⟩ := List.getElem?_eq_some_iff.mp hlookup
  have hextended : definition < (signature ++ suffix).length := by
    simp
    omega
  have harity : (signature ++ suffix).get ⟨definition, hextended⟩ = arity := by
    simpa [List.get_eq_getElem,
      List.getElem_append_left hdefinition] using hvalue
  unfold namedRel?
  rw [dif_pos hextended, dif_pos harity]
  congr 2
  apply Fin.ext
  simpa [NamedRenaming.appendRight] using hindex.symm

theorem compileNode?_appendRight
    (hwf : d.WellFormed signature) (suffix : List Nat)
    (context : WireContext d) (binders : BinderContext d rels)
    (node : Fin d.nodeCount) :
    compileNode? (signature ++ suffix) d context binders node =
      (compileNode? signature d context binders node).map
        (Item.renameNamed (NamedRenaming.appendRight signature suffix)) := by
  cases hnode : d.nodes node with
  | term region freePorts term =>
      cases houtput : resolvePort? d context node .output with
      | none => simp [compileNode?, hnode, houtput]
      | some output =>
          cases hfree : resolvePorts? d context node freePorts
              (fun index => .free index) with
          | none => simp [compileNode?, hnode, houtput, hfree]
          | some free =>
              simp [compileNode?, hnode, houtput, hfree, Item.renameNamed]
  | atom region binder =>
      cases hrelation : binders binder with
      | none => simp [compileNode?, hnode, hrelation]
      | some relation =>
          cases harguments : resolvePorts? d context node relation.1 with
          | none => simp [compileNode?, hnode, hrelation, harguments]
          | some arguments =>
              simp [compileNode?, hnode, hrelation, harguments,
                Item.renameNamed]
  | named region definition arity =>
      have hlookup := hwf.named_references_resolve node
      simp only [hnode] at hlookup
      obtain ⟨relation, hrelation⟩ := namedRel?_complete hlookup
      have hextended := namedRel?_appendRight (suffix := suffix) hrelation
      cases harguments : resolvePorts? d context node arity with
      | none =>
          simp [compileNode?, hnode, hrelation, hextended, harguments]
      | some arguments =>
          simp [compileNode?, hnode, hrelation, hextended, harguments,
            Item.renameNamed]

theorem compileNode?_equivariant {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hwires : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetNodup : targetContext.Nodup)
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : BinderContextsAgree iso sourceBinders targetBinders)
    (node : Fin source.nodeCount)
    {sourceItem : Item signature sourceContext.length rels}
    {targetItem : Item signature targetContext.length rels}
    (hsource : compileNode? signature source sourceContext sourceBinders node =
      some sourceItem)
    (htargetResult : compileNode? signature target targetContext targetBinders
      (iso.nodes node) = some targetItem) :
    ItemIso signature ambient rels sourceItem targetItem := by
  unfold compileNode? at hsource htargetResult
  rw [<- iso.nodes_eq node] at htargetResult
  cases hnode : source.nodes node with
  | term region freePorts term =>
      simp only [hnode, CNode.rename] at hsource htargetResult
      cases hsourceOutput : resolvePort? source sourceContext node .output with
      | none => simp [hsourceOutput] at hsource
      | some sourceOutput =>
          cases hsourceFree : resolvePorts? source sourceContext node freePorts
              (fun index => .free index) with
          | none => simp [hsourceOutput, hsourceFree] at hsource
          | some sourceFree =>
              simp [hsourceOutput, hsourceFree] at hsource
              subst sourceItem
              cases htargetOutput : resolvePort? target targetContext
                  (iso.nodes node) .output with
              | none => simp [htargetOutput] at htargetResult
              | some targetOutput =>
                  cases htargetFree : resolvePorts? target targetContext
                      (iso.nodes node) freePorts (fun index => .free index) with
                  | none =>
                      simp [htargetOutput, htargetFree] at htargetResult
                  | some targetFree =>
                      simp [htargetOutput, htargetFree] at htargetResult
                      subst targetItem
                      apply ItemIso.equation
                      · exact resolvePort?_equivariant iso htarget hwires
                          htargetNodup node .output hsourceOutput htargetOutput
                      · rw [Lambda.Term.mapFree_comp]
                        apply congrArg term.mapFree
                        exact resolvePorts?_equivariant iso htarget hwires
                          htargetNodup node freePorts (fun index => .free index)
                          hsourceFree htargetFree
  | atom region binder =>
      simp only [hnode, CNode.rename] at hsource htargetResult
      cases hsourceRelation : sourceBinders binder with
      | none => simp [hsourceRelation] at hsource
      | some sourceRelation =>
          have htargetRelation : targetBinders (iso.regions binder) =
              some sourceRelation := by rw [hbinders, hsourceRelation]
          cases sourceRelation with
          | mk arity relation =>
              cases hsourceArguments : resolvePorts? source sourceContext node arity
                  (fun index => .arg index) with
              | none => simp [hsourceRelation, hsourceArguments] at hsource
              | some sourceArguments =>
                  simp [hsourceRelation, hsourceArguments] at hsource
                  subst sourceItem
                  cases htargetArguments : resolvePorts? target targetContext
                      (iso.nodes node) arity (fun index => .arg index) with
                  | none =>
                      simp [htargetRelation, htargetArguments] at htargetResult
                  | some targetArguments =>
                      simp [htargetRelation, htargetArguments] at htargetResult
                      subst targetItem
                      apply ItemIso.atom relation
                      exact resolvePorts?_equivariant iso htarget hwires
                        htargetNodup node arity (fun index => .arg index)
                        hsourceArguments htargetArguments
  | named region definition arity =>
      simp only [hnode, CNode.rename] at hsource htargetResult
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
                  (iso.nodes node) arity (fun index => .arg index) with
              | none => simp [hrelation, htargetArguments] at htargetResult
              | some targetArguments =>
                  simp [hrelation, htargetArguments] at htargetResult
                  subst targetItem
                  apply ItemIso.named relation
                  exact resolvePorts?_equivariant iso htarget hwires
                    htargetNodup node arity (fun index => .arg index)
                    hsourceArguments htargetArguments

/-- Compile one direct occurrence using the supplied recursive region compiler. -/
def compileOccurrenceWith?
    (signature : List Nat) (d : ConcreteDiagram)
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount) :
    Option (Item signature context.length rels) :=
  match occurrence with
  | .node node => compileNode? signature d context binders node
  | .child child =>
      match d.regions child with
      | .sheet => none
      | .cut _ => return .cut (← recurse child context binders)
      | .bubble _ arity =>
          return .bubble arity
            (← recurse child context (binders.push child arity))

/-- Compile an ordered list of direct occurrences. -/
def compileOccurrencesWith?
    (signature : List Nat) (d : ConcreteDiagram)
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels) :
    List (LocalOccurrence d.regionCount d.nodeCount) ->
      Option (ItemSeq signature context.length rels)
  | [] => some .nil
  | occurrence :: tail => do
      let item <- compileOccurrenceWith? signature d recurse context binders occurrence
      let rest <- compileOccurrencesWith? signature d recurse context binders tail
      pure (.cons item rest)

theorem compileOccurrenceWith?_appendRight
    (hwf : d.WellFormed signature) (suffix : List Nat)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) → (context : WireContext d) →
        BinderContext d rels → Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) → (context : WireContext d) →
        BinderContext d rels →
          Option (Region (signature ++ suffix) context.length rels))
    (hrecurse : ∀ {rels : RelCtx} (region : Fin d.regionCount)
      (context : WireContext d) (binders : BinderContext d rels),
      targetRecurse region context binders =
        (sourceRecurse region context binders).map
          (Region.renameNamed (NamedRenaming.appendRight signature suffix)))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount) :
    compileOccurrenceWith? (signature ++ suffix) d targetRecurse
        context binders occurrence =
      (compileOccurrenceWith? signature d sourceRecurse
        context binders occurrence).map
          (Item.renameNamed (NamedRenaming.appendRight signature suffix)) := by
  cases occurrence with
  | node node => exact compileNode?_appendRight hwf suffix context binders node
  | child child =>
      cases hregion : d.regions child with
      | sheet => simp [compileOccurrenceWith?, hregion]
      | cut parent =>
          have h := hrecurse child context binders
          cases hsource : sourceRecurse child context binders with
          | none =>
              simp [hsource] at h
              simp [compileOccurrenceWith?, hregion, hsource, h]
          | some body =>
              simp [hsource] at h
              simp [compileOccurrenceWith?, hregion, hsource, h,
                Item.renameNamed]
      | bubble parent arity =>
          have h := hrecurse child context (binders.push child arity)
          cases hsource : sourceRecurse child context
              (binders.push child arity) with
          | none =>
              simp [hsource] at h
              simp [compileOccurrenceWith?, hregion, hsource, h]
          | some body =>
              simp [hsource] at h
              simp [compileOccurrenceWith?, hregion, hsource, h,
                Item.renameNamed]

theorem compileOccurrencesWith?_appendRight
    (hwf : d.WellFormed signature) (suffix : List Nat)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) → (context : WireContext d) →
        BinderContext d rels → Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) → (context : WireContext d) →
        BinderContext d rels →
          Option (Region (signature ++ suffix) context.length rels))
    (hrecurse : ∀ {rels : RelCtx} (region : Fin d.regionCount)
      (context : WireContext d) (binders : BinderContext d rels),
      targetRecurse region context binders =
        (sourceRecurse region context binders).map
          (Region.renameNamed (NamedRenaming.appendRight signature suffix)))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount)) :
    compileOccurrencesWith? (signature ++ suffix) d targetRecurse
        context binders occurrences =
      (compileOccurrencesWith? signature d sourceRecurse
        context binders occurrences).map
          (ItemSeq.renameNamed (NamedRenaming.appendRight signature suffix)) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence tail ih =>
      have hhead := compileOccurrenceWith?_appendRight hwf suffix
        sourceRecurse targetRecurse hrecurse context binders occurrence
      cases hsourceHead : compileOccurrenceWith? signature d sourceRecurse
          context binders occurrence with
      | none =>
          simp [hsourceHead] at hhead
          simp [compileOccurrencesWith?, hsourceHead, hhead]
      | some head =>
          simp [hsourceHead] at hhead
          cases hsourceTail : compileOccurrencesWith? signature d sourceRecurse
              context binders tail with
          | none =>
              simp [hsourceTail] at ih
              simp [compileOccurrencesWith?, hsourceHead, hsourceTail,
                hhead, ih]
          | some rest =>
              simp [hsourceTail] at ih
              simp [compileOccurrencesWith?, hsourceHead, hsourceTail,
                hhead, ih, ItemSeq.renameNamed]

/-- Map a sequence compiler across an occurrence embedding when every
individual occurrence compiler commutes with the same wire renaming.  The
source and target diagrams and recursive compilers may differ. -/
theorem compileOccurrencesWith?_map
    {sourceDiagram targetDiagram : ConcreteDiagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : WireContext sourceDiagram) → BinderContext sourceDiagram rels →
      Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin targetDiagram.regionCount) →
      (context : WireContext targetDiagram) → BinderContext targetDiagram rels →
      Option (Region signature context.length rels))
    (sourceContext : WireContext sourceDiagram)
    (targetContext : WireContext targetDiagram)
    (sourceBinders : BinderContext sourceDiagram rels)
    (targetBinders : BinderContext targetDiagram rels)
    (mapOccurrence : LocalOccurrence sourceDiagram.regionCount
        sourceDiagram.nodeCount →
      LocalOccurrence targetDiagram.regionCount targetDiagram.nodeCount)
    (wire : Fin sourceContext.length → Fin targetContext.length)
    (sourceOccurrences : List
      (LocalOccurrence sourceDiagram.regionCount sourceDiagram.nodeCount))
    (hoccurrence : ∀ occurrence, occurrence ∈ sourceOccurrences →
      compileOccurrenceWith? signature targetDiagram targetRecurse
          targetContext targetBinders (mapOccurrence occurrence) =
        (compileOccurrenceWith? signature sourceDiagram sourceRecurse
          sourceContext sourceBinders occurrence).map (Item.renameWires wire)) :
    compileOccurrencesWith? signature targetDiagram targetRecurse
        targetContext targetBinders (sourceOccurrences.map mapOccurrence) =
      (compileOccurrencesWith? signature sourceDiagram sourceRecurse
        sourceContext sourceBinders sourceOccurrences).map
          (ItemSeq.renameWires wire) := by
  induction sourceOccurrences with
  | nil => rfl
  | cons occurrence tail ih =>
      have hhead := hoccurrence occurrence (by simp)
      have htail : ∀ current, current ∈ tail →
          compileOccurrenceWith? signature targetDiagram targetRecurse
              targetContext targetBinders (mapOccurrence current) =
            (compileOccurrenceWith? signature sourceDiagram sourceRecurse
              sourceContext sourceBinders current).map
                (Item.renameWires wire) := by
        intro current hmem
        exact hoccurrence current (by simp [hmem])
      specialize ih htail
      cases hsourceHead : compileOccurrenceWith? signature sourceDiagram
          sourceRecurse sourceContext sourceBinders occurrence with
      | none =>
          simp [hsourceHead] at hhead
          simp [compileOccurrencesWith?, hsourceHead, hhead]
      | some head =>
          simp [hsourceHead] at hhead
          cases hsourceTail : compileOccurrencesWith? signature sourceDiagram
              sourceRecurse sourceContext sourceBinders tail with
          | none =>
              simp [hsourceTail] at ih
              simp [compileOccurrencesWith?, hsourceHead, hsourceTail,
                hhead, ih]
          | some rest =>
              simp [hsourceTail] at ih
              simp [compileOccurrencesWith?, hsourceHead, hsourceTail,
                hhead, ih, ItemSeq.renameWires]

theorem compileOccurrencesWith?_append
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (first second : List (LocalOccurrence d.regionCount d.nodeCount))
    (firstItems secondItems : ItemSeq signature context.length rels)
    (hfirst : compileOccurrencesWith? signature d recurse context binders first =
      some firstItems)
    (hsecond : compileOccurrencesWith? signature d recurse context binders second =
      some secondItems) :
    compileOccurrencesWith? signature d recurse context binders
        (first ++ second) =
      some (firstItems.append secondItems) := by
  induction first generalizing firstItems with
  | nil =>
      simp only [compileOccurrencesWith?] at hfirst
      cases hfirst
      simpa using hsecond
  | cons occurrence tail ih =>
      simp only [compileOccurrencesWith?] at hfirst ⊢
      cases hitem : compileOccurrenceWith? signature d recurse context binders
          occurrence with
      | none => simp [hitem] at hfirst
      | some item =>
          cases htail : compileOccurrencesWith? signature d recurse context binders
              tail with
          | none => simp [hitem, htail] at hfirst
          | some tailItems =>
              simp [hitem, htail] at hfirst
              cases hfirst
              change (do
                let compiled ← compileOccurrenceWith? signature d recurse
                  context binders occurrence
                let rest ← compileOccurrencesWith? signature d recurse
                  context binders (tail ++ second)
                pure (ItemSeq.cons compiled rest)) = _
              rw [hitem, ih tailItems htail]
              rfl

/-- Invert a successful compilation over an appended occurrence list into
successful prefix and suffix compilations and the corresponding item-sequence
append. -/
theorem compileOccurrencesWith?_append_split
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (first second : List (LocalOccurrence d.regionCount d.nodeCount))
    (items : ItemSeq signature context.length rels)
    (hitems : compileOccurrencesWith? signature d recurse context binders
      (first ++ second) = some items) :
    ∃ firstItems secondItems,
      compileOccurrencesWith? signature d recurse context binders first =
        some firstItems ∧
      compileOccurrencesWith? signature d recurse context binders second =
        some secondItems ∧
      items = firstItems.append secondItems := by
  induction first generalizing items with
  | nil =>
      exact ⟨.nil, items, rfl, hitems, by rfl⟩
  | cons occurrence tail ih =>
      simp only [List.cons_append, compileOccurrencesWith?] at hitems
      cases hhead : compileOccurrenceWith? signature d recurse context binders
          occurrence with
      | none => simp [hhead] at hitems
      | some head =>
          cases hrest : compileOccurrencesWith? signature d recurse context
              binders (tail ++ second) with
          | none => simp [hhead, hrest] at hitems
          | some rest =>
              simp [hhead, hrest] at hitems
              subst items
              obtain ⟨tailItems, secondItems, htail, hsecond, hrestEq⟩ :=
                ih rest hrest
              subst rest
              exact ⟨.cons head tailItems, secondItems,
                by simp [compileOccurrencesWith?, hhead, htail], hsecond, rfl⟩

theorem compileOccurrencesWith?_length
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : ItemSeq signature context.length rels}
    (h : compileOccurrencesWith? signature d recurse context binders occurrences =
      some items) :
    items.length = occurrences.length := by
  induction occurrences generalizing items with
  | nil => simp [compileOccurrencesWith?] at h; subst items; rfl
  | cons occurrence tail ih =>
      simp only [compileOccurrencesWith?] at h
      cases hitem : compileOccurrenceWith? signature d recurse context binders occurrence with
      | none => simp [hitem] at h
      | some item =>
          cases hrest : compileOccurrencesWith? signature d recurse context binders tail with
          | none => simp [hitem, hrest] at h
          | some rest =>
              simp [hitem, hrest] at h
              subst items
              simp only [ItemSeq.length, List.length_cons, Nat.succ.injEq]
              exact ih hrest

theorem compileOccurrencesWith?_get
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : ItemSeq signature context.length rels}
    (h : compileOccurrencesWith? signature d recurse context binders occurrences =
      some items) (index : Fin occurrences.length) :
    compileOccurrenceWith? signature d recurse context binders
        (occurrences.get index) =
      some (items.get (Fin.cast
        (compileOccurrencesWith?_length recurse context binders h).symm index)) := by
  induction occurrences generalizing items with
  | nil => exact Fin.elim0 index
  | cons occurrence tail ih =>
      simp only [compileOccurrencesWith?] at h
      cases hitem : compileOccurrenceWith? signature d recurse context binders occurrence with
      | none => simp [hitem] at h
      | some item =>
          cases hrest : compileOccurrencesWith? signature d recurse context binders tail with
          | none => simp [hitem, hrest] at h
          | some rest =>
              simp [hitem, hrest] at h
              subst items
              refine Fin.cases ?_ (fun tailIndex => ?_) index
              · simpa only [List.get, ItemSeq.get] using hitem
              · have ihResult := ih hrest tailIndex
                simpa only [List.get, ItemSeq.get] using ihResult

/-- Assemble pointwise compiler correctness over an explicit occurrence
equivalence into correctness of the compiled item sequences.  This is the
public seam used when two root compilers have different ambient/local
partitions (notably open roots): it does not assume those partitions have the
same cardinalities, only that the supplied total wire equivalence and each
compiled occurrence agree. -/
theorem compileOccurrencesWith?_iso
    {sourceDiagram targetDiagram : ConcreteDiagram}
    {rels : RelCtx}
    (sourceRecurse : forall {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : WireContext sourceDiagram) →
      BinderContext sourceDiagram rels →
      Option (Region signature context.length rels))
    (targetRecurse : forall {rels : RelCtx},
      (region : Fin targetDiagram.regionCount) →
      (context : WireContext targetDiagram) →
      BinderContext targetDiagram rels →
      Option (Region signature context.length rels))
    (sourceContext : WireContext sourceDiagram)
    (targetContext : WireContext targetDiagram)
    (sourceBinders : BinderContext sourceDiagram rels)
    (targetBinders : BinderContext targetDiagram rels)
    (sourceOccurrences : List
      (LocalOccurrence sourceDiagram.regionCount sourceDiagram.nodeCount))
    (targetOccurrences : List
      (LocalOccurrence targetDiagram.regionCount targetDiagram.nodeCount))
    {sourceItems : ItemSeq signature sourceContext.length rels}
    {targetItems : ItemSeq signature targetContext.length rels}
    (hsource : compileOccurrencesWith? signature sourceDiagram sourceRecurse
      sourceContext sourceBinders sourceOccurrences =
        some sourceItems)
    (htarget : compileOccurrencesWith? signature targetDiagram targetRecurse
      targetContext targetBinders targetOccurrences =
        some targetItems)
    (occurrences : FiniteEquiv (Fin sourceOccurrences.length)
      (Fin targetOccurrences.length))
    (wire : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length))
    (hitem : ∀ index : Fin sourceOccurrences.length,
      ItemIso signature wire rels
        (sourceItems.get
          (Fin.cast (compileOccurrencesWith?_length sourceRecurse
            sourceContext sourceBinders hsource).symm index))
        (targetItems.get
          (Fin.cast (compileOccurrencesWith?_length targetRecurse
            targetContext targetBinders htarget).symm (occurrences index)))) :
    ItemSeqIso signature wire rels sourceItems targetItems := by
  have hsourceLength := compileOccurrencesWith?_length sourceRecurse
    sourceContext sourceBinders hsource
  have htargetLength := compileOccurrencesWith?_length targetRecurse
    targetContext targetBinders htarget
  let positions := (FiniteEquiv.finCast hsourceLength).trans
    (occurrences.trans (FiniteEquiv.finCast htargetLength.symm))
  apply ItemSeqIso.permute positions
  intro sourceIndex
  let occurrenceIndex := Fin.cast hsourceLength sourceIndex
  have hsourcePosition :
      Fin.cast hsourceLength.symm occurrenceIndex = sourceIndex := by
    apply Fin.ext
    rfl
  have htargetPosition :
      Fin.cast htargetLength.symm (occurrences occurrenceIndex) =
        positions sourceIndex := by
    apply Fin.ext
    rfl
  simpa only [hsourcePosition, htargetPosition] using hitem occurrenceIndex

theorem compileOccurrencesWith?_complete
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (hsuccess : forall occurrence, occurrence ∈ occurrences →
      exists item,
        compileOccurrenceWith? signature d recurse context binders occurrence =
          some item) :
    exists items,
      compileOccurrencesWith? signature d recurse context binders occurrences =
        some items := by
  induction occurrences with
  | nil => exact ⟨.nil, rfl⟩
  | cons occurrence tail ih =>
      obtain ⟨item, hitem⟩ := hsuccess occurrence (by simp)
      obtain ⟨rest, hrest⟩ := ih (by
        intro candidate hcandidate
        exact hsuccess candidate (by simp [hcandidate]))
      exact ⟨.cons item rest, by
        simp [compileOccurrencesWith?, hitem, hrest]⟩

end VisualProof.Diagram.ConcreteElaboration
