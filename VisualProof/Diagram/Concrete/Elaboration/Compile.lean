import VisualProof.Diagram.Concrete.Elaboration.Context
import VisualProof.Diagram.Concrete.Examples
import VisualProof.Diagram.Concrete.Isomorphism

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

/-! Constructive restrictions of a finite equivalence to nodup list fibers. -/

private def restrictedIndex
    [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (index : Fin source.length) : Fin target.length :=
  (indexOf? target (equivalence source[index])).get (by
    rw [indexOf?_isSome_iff]
    exact (mem_iff source[index]).mpr (List.getElem_mem ..))

private theorem restrictedIndex_spec
    [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (index : Fin source.length) :
    target.get (restrictedIndex equivalence source target mem_iff index) =
      equivalence (source.get index) := by
  unfold restrictedIndex
  let hsome : (indexOf? target (equivalence source[index])).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact (mem_iff source[index]).mpr (List.getElem_mem ..)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    target.get ((indexOf? target (equivalence source[index])).get _) =
        target.get found := congrArg target.get
          (Option.get_of_eq_some hsome hfound)
    _ = equivalence (source.get index) := by
      simpa only [List.get_eq_getElem] using indexOf?_sound hfound

private theorem restricted_inverse_mem_iff
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (y : beta) : equivalence.symm y ∈ source ↔ y ∈ target := by
  constructor
  · intro hsource
    have := (mem_iff (equivalence.symm y)).mpr hsource
    rwa [FiniteEquiv.apply_symm_apply] at this
  · intro htarget
    apply (mem_iff (equivalence.symm y)).mp
    rwa [FiniteEquiv.apply_symm_apply]

private def restrictedEquiv
    [DecidableEq alpha] [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source) :
    FiniteEquiv (Fin source.length) (Fin target.length) where
  toFun := restrictedIndex equivalence source target mem_iff
  invFun := restrictedIndex equivalence.symm target source
    (restricted_inverse_mem_iff equivalence source target mem_iff)
  left_inv := by
    intro index
    have houter := restrictedIndex_spec equivalence.symm target source
      (restricted_inverse_mem_iff equivalence source target mem_iff)
      (restrictedIndex equivalence source target mem_iff index)
    have hinner := restrictedIndex_spec equivalence source target mem_iff index
    rw [hinner, FiniteEquiv.symm_apply_apply] at houter
    apply Fin.ext
    exact (List.getElem_inj sourceNodup).mp (by
      simpa only [List.get_eq_getElem] using houter)
  right_inv := by
    intro index
    have houter := restrictedIndex_spec equivalence source target mem_iff
      (restrictedIndex equivalence.symm target source
        (restricted_inverse_mem_iff equivalence source target mem_iff) index)
    have hinner := restrictedIndex_spec equivalence.symm target source
      (restricted_inverse_mem_iff equivalence source target mem_iff) index
    rw [hinner, FiniteEquiv.apply_symm_apply] at houter
    apply Fin.ext
    exact (List.getElem_inj targetNodup).mp (by
      simpa only [List.get_eq_getElem] using houter)

private theorem restrictedEquiv_spec
    [DecidableEq alpha] [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (index : Fin source.length) :
    target.get (restrictedEquiv equivalence source target sourceNodup targetNodup
      mem_iff index) = equivalence (source.get index) :=
  restrictedIndex_spec equivalence source target mem_iff index

private def renameOccurrence {source target : ConcreteDiagram}
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

private def localWireEquiv {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (exactScopeWires source region).length)
      (Fin (exactScopeWires target (iso.regions region)).length) :=
  restrictedEquiv iso.wires _ _
    (exactScopeWires_nodup source region)
    (exactScopeWires_nodup target (iso.regions region))
    (exactScopeWires_mem_iff iso region)

private theorem localWireEquiv_spec {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount)
    (index : Fin (exactScopeWires source region).length) :
    (exactScopeWires target (iso.regions region)).get
        (localWireEquiv iso region index) =
      iso.wires ((exactScopeWires source region).get index) :=
  restrictedEquiv_spec iso.wires _ _ _ _ _ index

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

private def localOccurrenceEquiv {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount) :
    FiniteEquiv
      (Fin (localOccurrences source region).length)
      (Fin (localOccurrences target (iso.regions region)).length) :=
  restrictedEquiv (occurrenceEquiv iso) _ _
    (localOccurrences_nodup source region)
    (localOccurrences_nodup target (iso.regions region))
    (localOccurrences_mem_iff iso region)

private theorem localOccurrenceEquiv_spec {source target : ConcreteDiagram}
    (iso : ConcreteIso source target) (region : Fin source.regionCount)
    (index : Fin (localOccurrences source region).length) :
    (localOccurrences target (iso.regions region)).get
        (localOccurrenceEquiv iso region index) =
      renameOccurrence iso ((localOccurrences source region).get index) :=
  restrictedEquiv_spec (occurrenceEquiv iso) _ _ _ _ _ index

private def WireContextsAgree {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)) : Prop :=
  forall index, targetContext.get (ambient index) =
    iso.wires (sourceContext.get index)

private def BinderContextsAgree {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (sourceContext : BinderContext source rels)
    (targetContext : BinderContext target rels) : Prop :=
  forall binder, targetContext (iso.regions binder) = sourceContext binder

private theorem BinderContextsAgree.push {source target : ConcreteDiagram}
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

private def castFinEquiv {source target source' target' : Nat}
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

private def extendedContextEquiv {source target : ConcreteDiagram}
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

private theorem get_append_castAdd (initial : List alpha) (suffix : List alpha)
    (index : Fin initial.length) :
    (initial ++ suffix).get
        (Fin.cast (by simp) (Fin.castAdd suffix.length index)) =
      initial.get index := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left index.isLt

private theorem get_append_natAdd (initial : List alpha) (suffix : List alpha)
    (index : Fin suffix.length) :
    (initial ++ suffix).get
        (Fin.cast (by simp) (Fin.natAdd initial.length index)) =
      suffix.get index := by
  simp [List.get_eq_getElem]

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

private theorem WireContextsAgree.extend {source target : ConcreteDiagram}
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

private def compileNode? (signature : List Nat) (d : ConcreteDiagram)
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

private theorem compileNode?_equivariant {source target : ConcreteDiagram}
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

private def compileOccurrenceWith?
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

private def compileOccurrencesWith?
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

private theorem compileOccurrencesWith?_length
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

private theorem compileOccurrencesWith?_get
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

private def finishRegion (d : ConcreteDiagram)
    (context : WireContext d) (region : Fin d.regionCount)
    (items : ItemSeq signature (context.extend region).length rels) :
    Region signature context.length rels := by
  rw [WireContext.length_extend] at items
  exact .mk (exactScopeWires d region).length items

private def castItemSeq (equality : sourceWires = targetWires)
    (items : ItemSeq signature sourceWires rels) :
    ItemSeq signature targetWires rels :=
  Eq.mp (congrArg (fun wires => ItemSeq signature wires rels) equality) items

private theorem regionIso_of_cast
    {sourceOuter targetOuter sourceLocal targetLocal
      sourceExtended targetExtended : Nat}
    (sourceEq : sourceExtended = sourceOuter + sourceLocal)
    (targetEq : targetExtended = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq signature sourceExtended rels)
    (targetItems : ItemSeq signature targetExtended rels)
    (hitems : ItemSeqIso signature
      (castFinEquiv sourceEq targetEq
        (extendWireEquiv ambient localEquiv)) rels
      sourceItems targetItems) :
    RegionIso signature ambient rels
      (.mk sourceLocal (castItemSeq sourceEq sourceItems))
      (.mk targetLocal (castItemSeq targetEq targetItems)) := by
  subst sourceExtended
  subst targetExtended
  simpa using RegionIso.mk localEquiv hitems

private def compileRegion? (signature : List Nat) (d : ConcreteDiagram) :
    Nat -> (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels)
  | 0, _, _, _ => none
  | fuel + 1, region, context, binders => do
      let extended := context.extend region
      let items <- compileOccurrencesWith? signature d
        (compileRegion? signature d fuel) extended binders
        (localOccurrences d region)
      pure (finishRegion d context region items)

private theorem compileRegion?_equivariant {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {fuel : Nat} {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hwires : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetExact : (targetContext.extend (iso.regions region)).Exact
      (iso.regions region))
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : BinderContextsAgree iso sourceBinders targetBinders)
    {sourceBody : Region signature sourceContext.length rels}
    {targetBody : Region signature targetContext.length rels}
    (hsource : compileRegion? signature source fuel region sourceContext
      sourceBinders = some sourceBody)
    (htargetResult : compileRegion? signature target fuel (iso.regions region)
      targetContext targetBinders = some targetBody) :
    RegionIso signature ambient rels sourceBody targetBody := by
  induction fuel generalizing region sourceContext targetContext rels
      sourceBinders targetBinders sourceBody targetBody with
  | zero => simp [compileRegion?] at hsource
  | succ fuel ih =>
      let sourceExtended := sourceContext.extend region
      let targetExtended := targetContext.extend (iso.regions region)
      let extended := extendedContextEquiv iso sourceContext targetContext
        ambient region
      have hwiresExtended : WireContextsAgree iso sourceExtended targetExtended
          extended := by
        exact WireContextsAgree.extend hwires region
      have hoccurrence : forall
          (occurrence : LocalOccurrence source.regionCount source.nodeCount)
          (_ : occurrence ∈ localOccurrences source region)
          (sourceItem : Item signature sourceExtended.length rels)
          (targetItem : Item signature targetExtended.length rels),
          compileOccurrenceWith? signature source
              (compileRegion? signature source fuel) sourceExtended sourceBinders
              occurrence = some sourceItem →
          compileOccurrenceWith? signature target
              (compileRegion? signature target fuel) targetExtended targetBinders
              (renameOccurrence iso occurrence) = some targetItem →
          ItemIso signature extended rels sourceItem targetItem := by
        intro occurrence hoccurrenceMem sourceItem targetItem
          hsourceItem htargetItem
        cases occurrence with
        | node node =>
            exact compileNode?_equivariant iso htarget hwiresExtended
              htargetExact.nodup hbinders node
              (by simpa [compileOccurrenceWith?] using hsourceItem)
              (by simpa [compileOccurrenceWith?, renameOccurrence] using htargetItem)
        | child child =>
            simp only [renameOccurrence, compileOccurrenceWith?]
              at hsourceItem htargetItem
            have hregionEq := iso.regions_eq child
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
                    (target.regions (iso.regions child)).parent? =
                      some (iso.regions region) := by
                  rw [<- hregionEq]
                  rfl
                have hchildExact := htargetExact.extend_child htarget hparentTarget
                rw [<- hregionEq] at htargetItem
                simp only [hchild] at hsourceItem htargetItem
                cases hsourceBody : compileRegion? signature source fuel child
                    sourceExtended sourceBinders with
                | none => simp [hsourceBody] at hsourceItem
                | some compiledSource =>
                    simp [hsourceBody] at hsourceItem
                    subst sourceItem
                    cases htargetBody : compileRegion? signature target fuel
                        (iso.regions child) targetExtended targetBinders with
                    | none => simp [htargetBody] at htargetItem
                    | some compiledTarget =>
                        simp [htargetBody] at htargetItem
                        subst targetItem
                        apply ItemIso.cut
                        exact ih hwiresExtended hchildExact hbinders
                          hsourceBody htargetBody
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
                    (target.regions (iso.regions child)).parent? =
                      some (iso.regions region) := by
                  rw [<- hregionEq]
                  rfl
                have hchildExact := htargetExact.extend_child htarget hparentTarget
                have hchildBinders := hbinders.push child arity
                rw [<- hregionEq] at htargetItem
                simp only [hchild] at hsourceItem htargetItem
                cases hsourceBody : compileRegion? signature source fuel child
                    sourceExtended (sourceBinders.push child arity) with
                | none => simp [hsourceBody] at hsourceItem
                | some compiledSource =>
                    simp [hsourceBody] at hsourceItem
                    subst sourceItem
                    cases htargetBody : compileRegion? signature target fuel
                        (iso.regions child) targetExtended
                        (targetBinders.push (iso.regions child) arity) with
                    | none => simp [htargetBody] at htargetItem
                    | some compiledTarget =>
                        simp [htargetBody] at htargetItem
                        subst targetItem
                        apply ItemIso.bubble
                        exact ih hwiresExtended hchildExact hchildBinders
                          hsourceBody htargetBody
      simp only [compileRegion?] at hsource htargetResult
      cases hsourceItems : compileOccurrencesWith? signature source
          (compileRegion? signature source fuel) sourceExtended sourceBinders
          (localOccurrences source region) with
      | none => simp [sourceExtended, hsourceItems] at hsource
      | some sourceItems =>
          simp [sourceExtended, hsourceItems] at hsource
          subst sourceBody
          cases htargetItems : compileOccurrencesWith? signature target
              (compileRegion? signature target fuel) targetExtended targetBinders
              (localOccurrences target (iso.regions region)) with
          | none => simp [targetExtended, htargetItems] at htargetResult
          | some targetItems =>
              simp [targetExtended, htargetItems] at htargetResult
              subst targetBody
              have hsourceLength := compileOccurrencesWith?_length
                (compileRegion? signature source fuel) sourceExtended
                sourceBinders hsourceItems
              have htargetLength := compileOccurrencesWith?_length
                (compileRegion? signature target fuel) targetExtended
                targetBinders htargetItems
              let positions : FiniteEquiv (Fin sourceItems.length)
                  (Fin targetItems.length) :=
                castFinEquiv hsourceLength htargetLength
                  (localOccurrenceEquiv iso region)
              have hitems : ItemSeqIso signature extended rels
                  sourceItems targetItems := by
                apply ItemSeqIso.permute positions
                intro sourceIndex
                let occurrenceIndex : Fin (localOccurrences source region).length :=
                  Fin.cast hsourceLength sourceIndex
                let targetOccurrenceIndex :=
                  localOccurrenceEquiv iso region occurrenceIndex
                have hsourceGet := compileOccurrencesWith?_get
                  (compileRegion? signature source fuel) sourceExtended
                  sourceBinders hsourceItems occurrenceIndex
                have htargetGet := compileOccurrencesWith?_get
                  (compileRegion? signature target fuel) targetExtended
                  targetBinders htargetItems targetOccurrenceIndex
                rw [localOccurrenceEquiv_spec iso region occurrenceIndex] at htargetGet
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
                extended, extendedContextEquiv] using
                regionIso_of_cast
                  (WireContext.length_extend sourceContext region)
                  (WireContext.length_extend targetContext (iso.regions region))
                  ambient (localWireEquiv iso region) sourceItems targetItems hitems

private theorem compileNode?_complete
    (hwf : d.WellFormed signature)
    {context : WireContext d} {binders : BinderContext d rels}
    {region : Fin d.regionCount}
    (hwires : context.Covers region) (hbinders : binders.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region) :
    exists item, compileNode? signature d context binders node = some item := by
  cases hnode : d.nodes node with
  | term nodeRegion freePorts term =>
      obtain ⟨output, houtput⟩ := checked_resolvePort?_complete hwf hwires
        (node := node) hregion (port := .output) (by
          simp [ConcreteDiagram.RequiresPort, hnode])
      obtain ⟨free, hfree⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion freePorts (fun index => .free index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨Item.equation output (term.mapFree free), by
        simp [compileNode?, hnode, houtput, hfree]⟩
  | atom nodeRegion binder =>
      have hnodeRegion : nodeRegion = region := by simpa [hnode] using hregion
      subst nodeRegion
      obtain ⟨parent, arity, hbubble⟩ :=
        BinderContext.checked_atom_binder_is_bubble hwf hnode
      obtain ⟨relation, hrelation⟩ :=
        BinderContext.checked_atom_binder_available hwf hbinders hnode hbubble
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode, hbubble]
          exact ⟨index, rfl⟩)
      exact ⟨Item.atom relation arguments, by
        simp [compileNode?, hnode, hrelation, harguments]⟩
  | named nodeRegion definition arity =>
      obtain ⟨relation, hrelation⟩ := checked_namedRel?_complete hwf hnode
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨Item.named relation arguments, by
        simp [compileNode?, hnode, hrelation, harguments]⟩

private theorem child_depth
    {d : ConcreteDiagram} {child parent : Fin d.regionCount} {depth : Nat}
    (hparent : (d.regions child).parent? = some parent)
    (hdepth : d.climb depth parent = some d.root) :
    d.climb (depth + 1) child = some d.root := by
  change d.climb (Nat.succ depth) child = some d.root
  simpa [ConcreteDiagram.climb, hparent] using hdepth

private theorem compileRegion?_complete
    (hwf : d.WellFormed signature)
    {fuel depth : Nat} {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (hdepth : d.climb depth region = some d.root)
    (hfuel : depth + fuel = d.regionCount + 1)
    (hwires : (context.extend region).Exact region)
    (hbinders : binders.Covers region) :
    exists body, compileRegion? signature d fuel region context binders = some body := by
  induction fuel generalizing depth region context rels with
  | zero =>
      have hpositive : 0 < d.regionCount + 1 - depth := by
        have hle := ParentTraversal.climb_to_root_steps_le_regionCount d
          hwf.root_is_sheet hwf.all_regions_reach_root hdepth
        omega
      exfalso
      omega
  | succ fuel ih =>
      let extended := context.extend region
      have hextended : extended.Exact region := by simpa [extended] using hwires
      have hoccurrence : forall occurrence,
          occurrence ∈ localOccurrences d region ->
          exists item,
            compileOccurrenceWith? signature d
              (compileRegion? signature d fuel) extended binders occurrence =
                some item := by
        intro occurrence hmem
        cases occurrence with
        | node node =>
            have hnodeRegion :=
              (mem_localOccurrences_node d region node).mp hmem
            simpa [compileOccurrenceWith?] using
              compileNode?_complete hwf hextended.covers hbinders hnodeRegion
        | child child =>
            have hparent :=
              (mem_localOccurrences_child d region child).mp hmem
            cases hchild : d.regions child with
            | sheet =>
                have hchildRoot : child = d.root :=
                  hwf.only_root_is_sheet child hchild
                subst child
                rw [hwf.root_is_sheet] at hparent
                simp [CRegion.parent?] at hparent
            | cut parent =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + fuel = d.regionCount + 1 := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.covers_cut_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨Item.cut body, by
                  simp [compileOccurrenceWith?, hchild, hbody]⟩
            | bubble parent arity =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + fuel = d.regionCount + 1 := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.push_covers_bubble_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨Item.bubble arity body, by
                  simp [compileOccurrenceWith?, hchild, hbody]⟩
      have hoccurrences : exists items,
          compileOccurrencesWith? signature d (compileRegion? signature d fuel)
            extended binders (localOccurrences d region) = some items := by
        have go : forall occurrences :
            List (LocalOccurrence d.regionCount d.nodeCount),
            (forall occurrence, occurrence ∈ occurrences ->
              exists item,
                compileOccurrenceWith? signature d
                    (compileRegion? signature d fuel) extended binders occurrence =
                  some item) ->
            exists items,
              compileOccurrencesWith? signature d (compileRegion? signature d fuel)
                extended binders occurrences = some items := by
          intro occurrences
          induction occurrences with
          | nil => intro _; exact ⟨.nil, rfl⟩
          | cons occurrence tail ihTail =>
              intro hsuccess
              obtain ⟨item, hitem⟩ := hsuccess occurrence (by simp)
              obtain ⟨rest, hrest⟩ := ihTail (by
                intro candidate hcandidate
                exact hsuccess candidate (by simp [hcandidate]))
              exact ⟨.cons item rest, by
                simp [compileOccurrencesWith?, hitem, hrest]⟩
        exact go _ hoccurrence
      obtain ⟨items, hitems⟩ := hoccurrences
      refine ⟨finishRegion d context region items, ?_⟩
      simp only [compileRegion?]
      change (compileOccurrencesWith? signature d (compileRegion? signature d fuel)
        extended binders (localOccurrences d region)).bind
          (fun result => some (finishRegion d context region result)) =
        some (finishRegion d context region items)
      rw [hitems]
      rfl

private theorem compileRoot?_complete (checked : CheckedDiagram signature) :
    exists body,
      compileRegion? signature checked.val (checked.val.regionCount + 1)
        checked.val.root ([] : WireContext checked.val)
        BinderContext.empty = some body := by
  apply compileRegion?_complete checked.property
    (depth := 0) (region := checked.val.root)
  · exact checked.val.climb_zero checked.val.root
  · omega
  · exact WireContext.root_exact checked.property
  · exact BinderContext.empty_covers_root checked.property

end VisualProof.Diagram.ConcreteElaboration

namespace VisualProof.Diagram

open ConcreteElaboration
open VisualProof.Theory

namespace CheckedDiagram

def elaborate (checked : CheckedDiagram signature) : Region signature 0 [] :=
  (compileRegion? signature checked.val (checked.val.regionCount + 1)
    checked.val.root ([] : WireContext checked.val) BinderContext.empty).get
      (Option.isSome_iff_exists.mpr (compileRoot?_complete checked))

private theorem elaborate_computation (checked : CheckedDiagram signature) :
    exists body,
      compileRegion? signature checked.val (checked.val.regionCount + 1)
          checked.val.root ([] : WireContext checked.val) BinderContext.empty =
        some body /\ checked.elaborate = body := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete checked
  refine ⟨body, hbody, ?_⟩
  simp [elaborate, hbody]

end CheckedDiagram

namespace ConcreteDiagram

def elaborate (d : ConcreteDiagram) (hwf : d.WellFormed signature) :
    Region signature 0 [] :=
  CheckedDiagram.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : ConcreteDiagram)
    (first second : d.WellFormed signature) :
    d.elaborate first = d.elaborate second := by
  rfl

private theorem elaborate_computation (d : ConcreteDiagram)
    (hwf : d.WellFormed signature) :
    exists body,
      compileRegion? signature d (d.regionCount + 1) d.root
          ([] : WireContext d) BinderContext.empty = some body /\
        d.elaborate hwf = body :=
  CheckedDiagram.elaborate_computation ⟨d, hwf⟩

end ConcreteDiagram

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
  rw [<- iso.regionCount_eq, <- iso.root_eq] at htargetKernel'
  have hwires : ConcreteElaboration.WireContextsAgree iso
      ([] : ConcreteElaboration.WireContext source)
      ([] : ConcreteElaboration.WireContext target)
      (.refl (Fin 0)) := by
    intro index
    exact Fin.elim0 index
  have htargetExact :
      ConcreteElaboration.WireContext.Exact
        (ConcreteElaboration.WireContext.extend
          ([] : ConcreteElaboration.WireContext target)
          (iso.regions source.root)) (iso.regions source.root) := by
    rw [iso.root_eq]
    exact ConcreteElaboration.WireContext.root_exact htarget
  have hbinders : ConcreteElaboration.BinderContextsAgree iso
      (ConcreteElaboration.BinderContext.empty :
        ConcreteElaboration.BinderContext source [])
      (ConcreteElaboration.BinderContext.empty :
        ConcreteElaboration.BinderContext target []) := by
    intro _
    rfl
  have hbody : RegionIso signature (.refl (Fin 0)) [] sourceBody targetBody :=
    ConcreteElaboration.compileRegion?_equivariant iso htarget hwires
      htargetExact hbinders hsourceKernel htargetKernel'
  rw [hsourceElaborate, htargetElaborate]
  exact hbody

end ConcreteIso

namespace ConcreteExamples

def validNestedChecked : CheckedDiagram [] :=
  ⟨validNested, checkWellFormed_iff.mp validNested_check⟩

def bareWireChecked : CheckedDiagram [] :=
  ⟨bareWire, checkWellFormed_iff.mp bareWire_check⟩

def unaryHead : RelVar [1] 1 where
  index := 0
  hasArity := rfl

def validNestedIntrinsic : Region [] 0 [] :=
  .mk 0 (.cons
    (.bubble 1 (.mk 1 (.cons
      (.cut (.mk 0 (.cons
        (.equation 0 (.lam (.bvar 0)))
        (.cons (.atom unaryHead (Fin.cases 0 Fin.elim0)) .nil))))
      .nil)))
    .nil)

theorem validNested_elaborate :
    validNestedChecked.elaborate = validNestedIntrinsic := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedDiagram.elaborate_computation validNestedChecked
  have hbody : body = validNestedIntrinsic := by
    have hkernel' := hkernel
    simp only [validNestedChecked] at hkernel'
    change some validNestedIntrinsic = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact helaborate.trans hbody

theorem bareWire_elaborate :
    bareWireChecked.elaborate = bareLocalWireExample := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedDiagram.elaborate_computation bareWireChecked
  have hbody : body = bareLocalWireExample := by
    have hkernel' := hkernel
    simp only [bareWireChecked] at hkernel'
    change some bareLocalWireExample = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact helaborate.trans hbody

theorem validNestedRelabeled_elaborate_isomorphic :
    Core.Isomorphic validNestedChecked.elaborate
      validNestedRelabeledChecked.elaborate := by
  exact validNestedRelabeledIso.elaborate_isomorphic
    (checkWellFormed_iff.mp validNested_check)
    validNestedRelabeled_wellFormed

end ConcreteExamples

end VisualProof.Diagram
