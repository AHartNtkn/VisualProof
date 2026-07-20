import VisualProof.Rule.Structural.InconsistentCut
import VisualProof.Rule.Soundness
import VisualProof.Rule.Soundness.Iteration.ExtractionTerminalSemantic
import VisualProof.Rule.Soundness.Iteration.SameSite
import VisualProof.Diagram.Concrete.Elaboration.Compile.Region
import VisualProof.Diagram.Isomorphism

namespace VisualProof.Rule.InconsistentCutSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

private def closeZeroPortTerm
    (term : Lambda.Term 0 (Fin 0)) : Lambda.ClosedTerm :=
  term.mapFree Fin.elim0

private theorem mapFree_closeZeroPortTerm
    (term : Lambda.Term 0 (Fin 0))
    (ports : Fin 0 → Fin wires) :
    term.mapFree ports =
      (closeZeroPortTerm term).mapFree Empty.elim := by
  rw [closeZeroPortTerm, Lambda.Term.mapFree_comp]
  apply congrArg term.mapFree
  funext impossible
  exact Fin.elim0 impossible

private theorem checked_zero_port_quote_ne
    {first second : Lambda.Term 0 (Fin 0)}
    (checked : Lambda.CheckedNormalSeparation first second) :
    Lambda.quote (closeZeroPortTerm first) ≠
      Lambda.quote (closeZeroPortTerm second) := by
  intro quotedEqual
  have closedEquivalent : Lambda.BetaEta
      (closeZeroPortTerm first) (closeZeroPortTerm second) :=
    Lambda.quote_eq_iff.mp quotedEqual
  have originalEquivalent :=
    closedEquivalent.mapFree (Empty.elim : Empty → Fin 0)
  have roundTrip :
      (Empty.elim : Empty → Fin 0) ∘ Fin.elim0 = id := by
    funext impossible
    exact Fin.elim0 impossible
  apply checked.not_betaEta
  simpa only [closeZeroPortTerm, Lambda.Term.mapFree_comp, roundTrip,
    Lambda.Term.mapFree_id] using originalEquivalent

private theorem shared_output_zero_port_terms_false
    {first second : Lambda.Term 0 (Fin 0)}
    (checked : Lambda.CheckedNormalSeparation first second) :
    ¬ ∃ output : Lambda.Individual,
      output = Lambda.quote (closeZeroPortTerm first) ∧
        output = Lambda.quote (closeZeroPortTerm second) := by
  rintro ⟨output, firstEq, secondEq⟩
  exact checked_zero_port_quote_ne checked (firstEq.symm.trans secondEq)

theorem direct_shared_output_equations_false
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {firstItem secondItem : Item signature context.length rels}
    (firstCompiled : compileNode? signature input.val context binders first =
      some firstItem)
    (secondCompiled : compileNode? signature input.val context binders second =
      some secondItem)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels) :
    ¬ (denoteItem Lambda.canonicalModel named env relEnv firstItem ∧
      denoteItem Lambda.canonicalModel named env relEnv secondItem) := by
  unfold compileNode? at firstCompiled secondCompiled
  rw [payload.firstNode] at firstCompiled
  rw [payload.secondNode] at secondCompiled
  cases firstOutputResult :
      resolvePort? input.val context first .output with
  | none => simp [firstOutputResult] at firstCompiled
  | some firstOutputIndex =>
      cases firstFreeResult : resolvePorts? input.val context first 0
          (fun index => .free index) with
      | none => simp [firstOutputResult, firstFreeResult] at firstCompiled
      | some firstFree =>
          simp [firstOutputResult, firstFreeResult] at firstCompiled
          subst firstItem
          cases secondOutputResult :
              resolvePort? input.val context second .output with
          | none => simp [secondOutputResult] at secondCompiled
          | some secondOutputIndex =>
              cases secondFreeResult : resolvePorts? input.val context second 0
                  (fun index => .free index) with
              | none =>
                  simp [secondOutputResult, secondFreeResult] at secondCompiled
              | some secondFree =>
                  simp [secondOutputResult, secondFreeResult] at secondCompiled
                  subst secondItem
                  have outputIndexEq : firstOutputIndex = secondOutputIndex := by
                    unfold resolvePort? at firstOutputResult secondOutputResult
                    cases firstOwnerResult :
                        endpointOwner? input.val ⟨first, .output⟩ with
                    | none => simp [firstOwnerResult] at firstOutputResult
                    | some firstOwner =>
                        cases secondOwnerResult :
                            endpointOwner? input.val ⟨second, .output⟩ with
                        | none => simp [secondOwnerResult] at secondOutputResult
                        | some secondOwner =>
                            simp [firstOwnerResult] at firstOutputResult
                            simp [secondOwnerResult] at secondOutputResult
                            have firstOwnerEq : payload.outputWire = firstOwner :=
                              endpointOwner?_unique
                                input.property.wire_endpoints_are_disjoint
                                firstOwnerResult payload.firstOutput
                            have secondOwnerEq : payload.outputWire = secondOwner :=
                              endpointOwner?_unique
                                input.property.wire_endpoints_are_disjoint
                                secondOwnerResult payload.secondOutput
                            rw [← firstOwnerEq] at firstOutputResult
                            rw [← secondOwnerEq] at secondOutputResult
                            exact Option.some.inj
                              (firstOutputResult.symm.trans secondOutputResult)
                  subst secondOutputIndex
                  rintro ⟨firstDenotes, secondDenotes⟩
                  change env firstOutputIndex =
                    Lambda.canonicalModel.eval
                      (payload.firstTerm.mapFree firstFree) env at firstDenotes
                  change env firstOutputIndex =
                    Lambda.canonicalModel.eval
                      (payload.secondTerm.mapFree secondFree) env at secondDenotes
                  rw [mapFree_closeZeroPortTerm,
                    Lambda.canonicalModel_eval_quoted] at firstDenotes
                  rw [mapFree_closeZeroPortTerm,
                    Lambda.canonicalModel_eval_quoted] at secondDenotes
                  exact shared_output_zero_port_terms_false checked
                    ⟨env firstOutputIndex, firstDenotes, secondDenotes⟩

theorem inconsistent_cut_items_false
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {items : ItemSeq signature context.length rels}
    (compiled : compileOccurrencesWith? signature input.val
      (compileRegion? signature input.val fuel) context binders
      (localOccurrences input.val region) = some items)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels) :
    ¬ denoteItemSeq Lambda.canonicalModel named env relEnv items := by
  have firstMember : LocalOccurrence.node first ∈
      localOccurrences input.val region := by
    rw [mem_localOccurrences_node]
    rw [payload.firstNode]
    rfl
  obtain ⟨firstOccurrenceIndex, firstOccurrenceIndexResult⟩ :=
    indexOf?_complete firstMember
  have firstOccurrenceEq :
      (localOccurrences input.val region).get firstOccurrenceIndex =
        .node first :=
    indexOf?_sound firstOccurrenceIndexResult
  let firstItemIndex := Fin.cast
    (compileOccurrencesWith?_length
      (compileRegion? signature input.val fuel) context binders compiled).symm
      firstOccurrenceIndex
  have firstCompiled : compileNode? signature input.val context binders first =
      some (items.get firstItemIndex) := by
    have atIndex := compileOccurrencesWith?_get
      (compileRegion? signature input.val fuel) context binders compiled
      firstOccurrenceIndex
    rw [firstOccurrenceEq] at atIndex
    exact atIndex
  have secondMember : LocalOccurrence.node second ∈
      localOccurrences input.val region := by
    rw [mem_localOccurrences_node]
    rw [payload.secondNode]
    rfl
  obtain ⟨secondOccurrenceIndex, secondOccurrenceIndexResult⟩ :=
    indexOf?_complete secondMember
  have secondOccurrenceEq :
      (localOccurrences input.val region).get secondOccurrenceIndex =
        .node second :=
    indexOf?_sound secondOccurrenceIndexResult
  let secondItemIndex := Fin.cast
    (compileOccurrencesWith?_length
      (compileRegion? signature input.val fuel) context binders compiled).symm
      secondOccurrenceIndex
  have secondCompiled :
      compileNode? signature input.val context binders second =
        some (items.get secondItemIndex) := by
    have atIndex := compileOccurrencesWith?_get
      (compileRegion? signature input.val fuel) context binders compiled
      secondOccurrenceIndex
    rw [secondOccurrenceEq] at atIndex
    exact atIndex
  intro itemsDenote
  have allItems :=
    (denoteItemSeq_iff_get Lambda.canonicalModel named env relEnv items).mp
      itemsDenote
  exact direct_shared_output_equations_false payload checked context binders
    firstCompiled secondCompiled named env relEnv
    ⟨allItems firstItemIndex, allItems secondItemIndex⟩

theorem inconsistent_cut_body_false
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {compiledCutBody : Region signature context.length rels}
    (compiled : compileRegion? signature input.val fuel region context binders =
      some compiledCutBody) :
    ∀ (named : NamedEnv Lambda.Individual signature)
      (env : Fin context.length → Lambda.Individual)
      (relEnv : RelEnv Lambda.Individual rels),
      ¬ denoteRegion Lambda.canonicalModel named env relEnv compiledCutBody := by
  intro named env relEnv bodyDenotes
  cases fuel with
  | zero => simp [compileRegion?] at compiled
  | succ remainingFuel =>
      simp only [compileRegion?] at compiled
      cases itemsResult : compileOccurrencesWith? signature input.val
          (compileRegion? signature input.val remainingFuel)
          (context.extend region) binders
          (localOccurrences input.val region) with
      | none => simp [itemsResult] at compiled
      | some items =>
          simp [itemsResult] at compiled
          subst compiledCutBody
          unfold finishRegion at bodyDenotes
          rw [denoteRegion_mk] at bodyDenotes
          obtain ⟨localEnv, castItemsDenote⟩ := bodyDenotes
          rw [ItemSeq.castWiresEq_eq_renameWires,
            denoteItemSeq_renameWires] at castItemsDenote
          exact inconsistent_cut_items_false payload checked
            (context.extend region) binders itemsResult named
            (extendWireEnv env localEnv ∘
              Fin.cast (WireContext.length_extend context region))
            relEnv castItemsDenote

theorem inconsistent_cut_item_true
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {compiledCutBody : Region signature context.length rels}
    (compiled : compileRegion? signature input.val fuel region context binders =
      some compiledCutBody)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItem Lambda.canonicalModel named env relEnv (.cut compiledCutBody) := by
  rw [cut_denotes_negation]
  exact inconsistent_cut_body_false payload checked context binders compiled
    named env relEnv

theorem inconsistent_cut_occurrence_compiles
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {compiledCutBody : Region signature context.length rels}
    (compiled : compileRegion? signature input.val fuel region context binders =
      some compiledCutBody) :
    compileOccurrenceWith? signature input.val
        (compileRegion? signature input.val fuel) context binders
        (.child region) =
      some (.cut compiledCutBody) := by
  simp [compileOccurrenceWith?, payload.region_is_cut, compiled]

theorem inconsistent_cut_compiled_item_true
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {compiledCutBody : Region signature context.length rels}
    (compiledBody : compileRegion? signature input.val fuel region context binders =
      some compiledCutBody)
    {compiledCutItem : Item signature context.length rels}
    (compiledItem : compileOccurrenceWith? signature input.val
      (compileRegion? signature input.val fuel) context binders
      (.child region) = some compiledCutItem)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItem Lambda.canonicalModel named env relEnv compiledCutItem := by
  have canonicalItem := inconsistent_cut_occurrence_compiles payload context
    binders compiledBody
  rw [canonicalItem] at compiledItem
  cases compiledItem
  exact inconsistent_cut_item_true payload checked context binders compiledBody
    named env relEnv

theorem inconsistent_cut_frame_iff
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {compiledCutBody : Region signature context.length rels}
    (compiled : compileRegion? signature input.val fuel region context binders =
      some compiledCutBody)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (before after : ItemSeq signature context.length rels) :
    denoteItemSeq Lambda.canonicalModel named env relEnv
        (before.append (.cons (.cut compiledCutBody) after)) ↔
      denoteItemSeq Lambda.canonicalModel named env relEnv
        (before.append after) := by
  have cutTrue := inconsistent_cut_item_true payload checked context binders
    compiled named env relEnv
  simp only [denoteItemSeq_append, denoteItemSeq_cons]
  constructor
  · rintro ⟨beforeDenotes, _, afterDenotes⟩
    exact ⟨beforeDenotes, afterDenotes⟩
  · rintro ⟨beforeDenotes, afterDenotes⟩
    exact ⟨beforeDenotes, cutTrue, afterDenotes⟩

theorem inconsistent_cut_compiled_frame_iff
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {compiledCutBody : Region signature context.length rels}
    (compiledBody : compileRegion? signature input.val fuel region context binders =
      some compiledCutBody)
    {compiledCutItem : Item signature context.length rels}
    (compiledItem : compileOccurrenceWith? signature input.val
      (compileRegion? signature input.val fuel) context binders
      (.child region) = some compiledCutItem)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (before after : ItemSeq signature context.length rels) :
    denoteItemSeq Lambda.canonicalModel named env relEnv
        (before.append (.cons compiledCutItem after)) ↔
      denoteItemSeq Lambda.canonicalModel named env relEnv
        (before.append after) := by
  have cutTrue := inconsistent_cut_compiled_item_true payload checked context
    binders compiledBody compiledItem named env relEnv
  simp only [denoteItemSeq_append, denoteItemSeq_cons]
  constructor
  · rintro ⟨beforeDenotes, _, afterDenotes⟩
    exact ⟨beforeDenotes, afterDenotes⟩
  · rintro ⟨beforeDenotes, afterDenotes⟩
    exact ⟨beforeDenotes, cutTrue, afterDenotes⟩

private theorem selected_occurrences_eq_singleton
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second) :
    ModalSoundness.selectedOccurrences input.val payload.selection =
      [.child region] := by
  have member_iff : ∀ occurrence,
      occurrence ∈ ModalSoundness.selectedOccurrences input.val
          payload.selection ↔
        occurrence = .child region := by
    intro occurrence
    cases occurrence with
    | node node =>
        simp [ModalSoundness.selectedOccurrences,
          ModalSoundness.occurrenceSelected, payload.selection_eq]
    | child child =>
        simp only [ModalSoundness.selectedOccurrences, List.mem_filter,
          ModalSoundness.occurrenceSelected, decide_eq_true_eq,
          LocalOccurrence.child.injEq]
        constructor
        · rintro ⟨_, selected⟩
          rw [payload.selection_eq] at selected
          simpa using selected
        · intro equality
          subst child
          refine ⟨?_, ?_⟩
          · simp [payload.selection_eq, payload.region_is_cut,
              CRegion.parent?]
          · rw [payload.selection_eq]
            simp
  have contains : LocalOccurrence.child region ∈
      ModalSoundness.selectedOccurrences input.val payload.selection :=
    (member_iff _).2 rfl
  generalize hselected : ModalSoundness.selectedOccurrences input.val
    payload.selection = selected at contains ⊢
  have selectedNodup : selected.Nodup := by
    rw [← hselected]
    unfold ModalSoundness.selectedOccurrences
    exact (localOccurrences_nodup input.val
      payload.selection.val.anchor).filter _
  cases selected with
  | nil => simp at contains
  | cons head tail =>
      simp only [List.nodup_cons] at selectedNodup
      have headEq : head = .child region :=
        (member_iff head).1 (by rw [hselected]; simp)
      subst head
      have tailEmpty : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro item itemMember
        have itemEq : item = .child region :=
          (member_iff item).1 (by rw [hselected]; simp [itemMember])
        subst item
        exact selectedNodup.1 itemMember
      subst tail
      rfl

private theorem selected_items_true
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    {fuel : Nat} {rels : RelCtx}
    (context : WireContext input.val)
    (binders : BinderContext input.val rels)
    {items : ItemSeq signature context.length rels}
    (compiled : compileOccurrencesWith? signature input.val
      (compileRegion? signature input.val fuel) context binders
      (ModalSoundness.selectedOccurrences input.val payload.selection) =
        some items)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItemSeq Lambda.canonicalModel named env relEnv items := by
  rw [selected_occurrences_eq_singleton payload] at compiled
  simp only [compileOccurrencesWith?] at compiled
  cases bodyResult : compileRegion? signature input.val fuel region context
      binders with
  | none =>
      simp [compileOccurrenceWith?, payload.region_is_cut, bodyResult] at compiled
  | some body =>
      simp [compileOccurrenceWith?, payload.region_is_cut, bodyResult] at compiled
      subst items
      simp only [denoteItemSeq_cons, denoteItemSeq_nil, and_true]
      exact inconsistent_cut_item_true payload checked context binders
        bodyResult named env relEnv

private def defaultIndividual : Lambda.Individual :=
  Lambda.quote Lambda.idTerm

private def falseRelEnv : (rels : RelCtx) → RelEnv Lambda.Individual rels
  | [] => PUnit.unit
  | _ :: rest => (⟨fun _ => False, falseRelEnv rest⟩)

private def relEnvOfLookup (ctx : RelCtx)
    (assignment : ∀ arity, RelVar ctx arity →
      Relation Lambda.Individual arity) : RelEnv Lambda.Individual ctx :=
  match ctx with
  | [] => PUnit.unit
  | head :: tail =>
      (assignment head ⟨0, rfl⟩,
        relEnvOfLookup tail (fun arity relation =>
          assignment arity (BinderContext.liftVar head relation)))

private theorem relEnvOfLookup_lookup (ctx : RelCtx)
    (assignment : ∀ arity, RelVar ctx arity →
      Relation Lambda.Individual arity)
    {arity} (relation : RelVar ctx arity) :
    (relEnvOfLookup ctx assignment).lookup relation =
      assignment arity relation := by
  induction ctx with
  | nil => exact Fin.elim0 relation.index
  | cons head tail ih =>
      rcases relation with ⟨index, hasArity⟩
      revert hasArity
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · intro hasArity
        subst arity
        rfl
      · intro hasArity
        simpa [relEnvOfLookup, RelEnv.lookup] using
          ih (fun arity relation => assignment arity
            (BinderContext.liftVar head relation))
            ⟨tailIndex, hasArity⟩

private noncomputable def extendRelEnv
    (rho : RelationRenaming source target)
    (sourceEnv : RelEnv Lambda.Individual source) :
    RelEnv Lambda.Individual target := by
  classical
  exact relEnvOfLookup target (fun arity targetRelation =>
    if witness : ∃ sourceRelation : RelVar source arity,
        rho sourceRelation = targetRelation then
      sourceEnv.lookup (Classical.choose witness)
    else
      fun _ => False)

private theorem extendRelEnv_agrees
    (rho : RelationRenaming source target)
    (injective : ∀ arity, Function.Injective (@rho arity))
    (sourceEnv : RelEnv Lambda.Individual source) :
    RelEnv.Agrees rho sourceEnv (extendRelEnv rho sourceEnv) := by
  intro arity sourceRelation
  unfold extendRelEnv
  dsimp only
  rw [relEnvOfLookup_lookup]
  let existsProof : ∃ candidate : RelVar source arity,
      rho candidate = rho sourceRelation := ⟨sourceRelation, rfl⟩
  rw [dif_pos existsProof]
  apply congrArg sourceEnv.lookup
  apply injective arity
  exact (Classical.choose_spec existsProof).symm

private theorem terminalRelationMap_injective
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : BinderContext input.val hostRels)
    (fragmentEnumeration : BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (hostEnumeration : BinderContext.Enumeration input.val hostBinders
      selection.val.anchor)
    (hostCover : hostBinders.Covers selection.val.anchor) :
    let witness := IterationSoundness.ExtractionBinderWitness.terminal input
      selection layout fragmentBinders fragmentEnumeration hostBinders
      hostCover
    ∀ arity, Function.Injective (@witness.relationMap arity) := by
  dsimp only
  let witness := IterationSoundness.ExtractionBinderWitness.terminal input
    selection layout fragmentBinders fragmentEnumeration hostBinders hostCover
  intro arity left right mappedEq
  have leftOwner := hostEnumeration.lookup_owner (witness.relationMap left)
    (witness.lookup left)
  have rightOwner := hostEnumeration.lookup_owner (witness.relationMap right)
    (witness.lookup right)
  have mappedIndexEq : (witness.relationMap left).index =
      (witness.relationMap right).index := congrArg RelVar.index mappedEq
  have originEq : IterationSoundness.extractionBinderOrigin input selection
      layout (fragmentEnumeration.binder left.index) =
    IterationSoundness.extractionBinderOrigin input selection layout
      (fragmentEnumeration.binder right.index) := by
    rw [← leftOwner, ← rightOwner, mappedIndexEq]
  obtain ⟨leftProxy, leftBinder⟩ :=
    IterationSoundness.extractionTerminalBinder_is_proxy input selection layout
      fragmentBinders fragmentEnumeration left.index
  obtain ⟨rightProxy, rightBinder⟩ :=
    IterationSoundness.extractionTerminalBinder_is_proxy input selection layout
      fragmentBinders fragmentEnumeration right.index
  rw [leftBinder, rightBinder,
    IterationSoundness.extractionBinderOrigin_proxy,
    IterationSoundness.extractionBinderOrigin_proxy] at originEq
  have proxyEq : leftProxy = rightProxy := by
    apply Fin.ext
    apply (List.getElem_inj selection.externalBinders_nodup).mp
    simpa only [layout.externalBinders_exact, List.get_eq_getElem] using
      originEq
  have binderEq : fragmentEnumeration.binder left.index =
      fragmentEnumeration.binder right.index := by
    rw [leftBinder, rightBinder, proxyEq]
  have indexEq := fragmentEnumeration.binder_injective binderEq
  rcases left with ⟨leftIndex, leftArity⟩
  rcases right with ⟨rightIndex, rightArity⟩
  dsimp only at indexEq
  subst rightIndex
  rfl

private noncomputable def extendHostEnvironment
    (map : Fin source → Fin target)
    (sourceEnv : Fin source → Lambda.Individual) :
    Fin target → Lambda.Individual := fun targetIndex =>
  if witness : ∃ sourceIndex, map sourceIndex = targetIndex then
    sourceEnv (Classical.choose witness)
  else
    defaultIndividual

private theorem extendHostEnvironment_map
    (map : Fin source → Fin target) (injective : Function.Injective map)
    (sourceEnv : Fin source → Lambda.Individual)
    (sourceIndex : Fin source) :
    extendHostEnvironment map sourceEnv (map sourceIndex) =
      sourceEnv sourceIndex := by
  unfold extendHostEnvironment
  let existsProof : ∃ candidate, map candidate = map sourceIndex :=
    ⟨sourceIndex, rfl⟩
  rw [dif_pos existsProof]
  apply congrArg sourceEnv
  apply injective
  exact Classical.choose_spec existsProof

private noncomputable def extractionHostIndexMap
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : WireContext input.val)
    (fragmentVisible : ∀ wire, wire ∈ fragmentContext →
      (input.val.extractDiagramRaw selection layout).Encloses
        ((input.val.extractDiagramRaw selection layout).wires wire).scope
        layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor) :
    Fin fragmentContext.length → Fin hostContext.length := fun index =>
  Classical.choose (indexOf?_complete (by
    apply (hostExact.mem_iff _).2
    exact IterationSoundness.fragmentWireOrigin_scope_encloses_anchor input
      selection layout (fragmentContext.get index)
        (fragmentVisible _ (List.get_mem fragmentContext index))))

private theorem extractionHostIndexMap_spec
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : WireContext input.val)
    (fragmentVisible : ∀ wire, wire ∈ fragmentContext →
      (input.val.extractDiagramRaw selection layout).Encloses
        ((input.val.extractDiagramRaw selection layout).wires wire).scope
        layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (index : Fin fragmentContext.length) :
    (IterationSoundness.extractionContextRelation input selection layout
      fragmentContext hostContext).Rel index
        (extractionHostIndexMap input selection layout fragmentContext
          hostContext fragmentVisible hostExact index) := by
  unfold IterationSoundness.extractionContextRelation extractionHostIndexMap
  exact (indexOf?_sound (Classical.choose_spec (indexOf?_complete (by
    apply (hostExact.mem_iff _).2
    exact IterationSoundness.fragmentWireOrigin_scope_encloses_anchor input
      selection layout (fragmentContext.get index)
        (fragmentVisible _ (List.get_mem fragmentContext index)))))).symm

private theorem extractionHostIndexMap_injective
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : WireContext input.val)
    (fragmentVisible : ∀ wire, wire ∈ fragmentContext →
      (input.val.extractDiagramRaw selection layout).Encloses
        ((input.val.extractDiagramRaw selection layout).wires wire).scope
        layout.bodyContainer)
    (fragmentNodup : fragmentContext.Nodup)
    (hostExact : hostContext.Exact selection.val.anchor) :
    Function.Injective (extractionHostIndexMap input selection layout
      fragmentContext hostContext fragmentVisible hostExact) := by
  intro left right equal
  have leftSpec := extractionHostIndexMap_spec input selection layout
    fragmentContext hostContext fragmentVisible hostExact left
  have rightSpec := extractionHostIndexMap_spec input selection layout
    fragmentContext hostContext fragmentVisible hostExact right
  unfold IterationSoundness.extractionContextRelation at leftSpec rightSpec
  rw [equal] at leftSpec
  apply Fin.ext
  apply (List.getElem_inj fragmentNodup).mp
  apply input.val.fragmentWireOrigin_injective selection layout
  exact leftSpec.trans rightSpec.symm

private theorem extractionEnvironmentsAgree_of_source
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : WireContext input.val)
    (fragmentVisible : ∀ wire, wire ∈ fragmentContext →
      (input.val.extractDiagramRaw selection layout).Encloses
        ((input.val.extractDiagramRaw selection layout).wires wire).scope
        layout.bodyContainer)
    (fragmentNodup : fragmentContext.Nodup)
    (hostExact : hostContext.Exact selection.val.anchor)
    (fragmentEnv : Fin fragmentContext.length → Lambda.Individual) :
    let indexMap := extractionHostIndexMap input selection layout
      fragmentContext hostContext fragmentVisible hostExact
    let hostEnv := extendHostEnvironment indexMap fragmentEnv
    (IterationSoundness.extractionContextRelation input selection layout
      fragmentContext hostContext).EnvironmentsAgree fragmentEnv hostEnv := by
  dsimp only
  intro fragmentIndex hostIndex related
  let indexMap := extractionHostIndexMap input selection layout
    fragmentContext hostContext fragmentVisible hostExact
  have chosen := extractionHostIndexMap_spec input selection layout
    fragmentContext hostContext fragmentVisible hostExact fragmentIndex
  have hostIndexEq : indexMap fragmentIndex = hostIndex := by
    apply Fin.ext
    apply (List.getElem_inj hostExact.nodup).mp
    unfold IterationSoundness.extractionContextRelation at chosen related
    exact chosen.symm.trans related
  rw [← hostIndexEq]
  exact (extendHostEnvironment_map indexMap
    (extractionHostIndexMap_injective input selection layout fragmentContext
      hostContext fragmentVisible fragmentNodup hostExact) fragmentEnv
      fragmentIndex).symm

private theorem extracted_root_true
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    (layout : FragmentLayout input.val payload.selection)
    (hzero : layout.proxyCount = 0)
    (pattern : Splice.Input.OpenRootCompilerItems
      ⟨input.val.extractOpenRaw payload.selection layout,
        ConcreteDiagram.extractOpenRaw_wellFormed input payload.selection
          layout⟩)
    (named : NamedEnv Lambda.Individual signature)
    (fragmentOuter : Fin
      (input.val.extractOpenRaw payload.selection layout).exposedWires.length →
        Lambda.Individual) :
    denoteRegion (relCtx := []) Lambda.canonicalModel named fragmentOuter
      (PUnit.unit : RelEnv Lambda.Individual [])
      (finishRoot
        (input.val.extractOpenRaw payload.selection layout).exposedWires
        (input.val.extractOpenRaw payload.selection layout).hiddenWires
        pattern.items) := by
  let host := Classical.choice
    (Splice.siteView_complete input payload.selection.val.anchor)
  let hostContext := host.compilerLeaf.inheritedWires.extend
    payload.selection.val.anchor
  have selectedLocal : ∀ occurrence,
      occurrence ∈ ModalSoundness.selectedOccurrences input.val
          payload.selection →
        occurrence ∈ localOccurrences input.val
          payload.selection.val.anchor := by
    intro occurrence member
    rw [ModalSoundness.selectedOccurrences, List.mem_filter] at member
    exact member.1
  obtain ⟨hostItems, hostCompiled⟩ := compileOccurrencesWith?_complete
    (compileRegion? signature input.val host.compilerLeaf.fuel)
    hostContext host.compilerLeaf.binders
    (ModalSoundness.selectedOccurrences input.val payload.selection) (by
      intro occurrence member
      exact ModalSoundness.compileOccurrence_success_of_mem input.val
        (compileRegion? signature input.val host.compilerLeaf.fuel)
        hostContext host.compilerLeaf.binders
        host.compilerLeaf.itemsComputation (selectedLocal occurrence member))
  have hostExact : hostContext.Exact payload.selection.val.anchor :=
    host.compilerLeaf.wiresExact
  let fragment := input.val.extractOpenRaw payload.selection layout
  have bodyEq : layout.bodyContainer = fragment.diagram.root :=
    layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero
  have fragmentVisible : ∀ wire, wire ∈ fragment.exposedWires →
      fragment.diagram.Encloses (fragment.diagram.wires wire).scope
        layout.bodyContainer := by
    intro wire member
    have scope := (ConcreteDiagram.extractOpenRaw_wellFormed input
      payload.selection layout).exposed_root_scoped member
    rw [scope, bodyEq]
    exact ConcreteDiagram.Encloses.refl _ _
  let indexMap := extractionHostIndexMap input payload.selection layout
    fragment.exposedWires hostContext fragmentVisible hostExact
  let hostEnv := extendHostEnvironment indexMap fragmentOuter
  let hostRelEnv := falseRelEnv host.intrinsicPath.toFocus.holeRels
  have hostDenotes : denoteItemSeq Lambda.canonicalModel named hostEnv
      hostRelEnv hostItems :=
    selected_items_true payload checked hostContext host.compilerLeaf.binders
      hostCompiled named hostEnv hostRelEnv
  have simulation := IterationSoundness.extractionCompileRoot_selected_denote
    input payload.selection layout hzero Lambda.canonicalModel named
      host.compilerLeaf.fuel hostContext host.compilerLeaf.binders
      host.compilerLeaf.binderEnumeration host.compilerLeaf.bindersCover
      hostExact pattern.items hostItems pattern.computation hostCompiled
  have agrees := extractionEnvironmentsAgree_of_source input payload.selection
    layout fragment.exposedWires hostContext fragmentVisible
    fragment.exposedWires_nodup hostExact fragmentOuter
  have renamed := simulation fragmentOuter hostEnv hostRelEnv agrees
    ((IterationSoundness.denoteRegion_mk_zero_iff Lambda.canonicalModel named
      hostEnv hostRelEnv
      hostItems).2 hostDenotes)
  let relationMap : RelationRenaming []
      host.intrinsicPath.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming _
  have unrenamed := (denoteRegion_renameRelations Lambda.canonicalModel named
    relationMap (RelEnv.pullback relationMap hostRelEnv) hostRelEnv
    (RelEnv.pullback_agrees relationMap hostRelEnv) fragmentOuter
    (finishRoot fragment.exposedWires fragment.hiddenWires
      pattern.items)).mp (by
        simpa [relationMap, fragment] using renamed)
  simpa using unrenamed

private theorem extracted_terminal_true
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    (layout : FragmentLayout input.val payload.selection)
    {fragmentRels : RelCtx}
    (fragmentBinders : BinderContext
      (input.val.extractDiagramRaw payload.selection layout) fragmentRels)
    (fragmentEnumeration : BinderContext.Enumeration
      (input.val.extractDiagramRaw payload.selection layout) fragmentBinders
      layout.bodyContainer)
    (fragmentContext : WireContext
      (input.val.extractDiagramRaw payload.selection layout))
    (fragmentExact : (fragmentContext.extend layout.bodyContainer).Exact
      layout.bodyContainer)
    (fragmentFuel : Nat)
    {fragmentItems : ItemSeq signature
      (fragmentContext.extend layout.bodyContainer).length fragmentRels}
    (fragmentCompiled : compileOccurrencesWith? signature
      (input.val.extractDiagramRaw payload.selection layout)
      (compileRegion? signature
        (input.val.extractDiagramRaw payload.selection layout)
        fragmentFuel)
      (fragmentContext.extend layout.bodyContainer) fragmentBinders
      (localOccurrences (input.val.extractDiagramRaw payload.selection layout)
        layout.bodyContainer) = some fragmentItems)
    (named : NamedEnv Lambda.Individual signature)
    (fragmentOuter : Fin fragmentContext.length → Lambda.Individual)
    (fragmentRelEnv : RelEnv Lambda.Individual fragmentRels) :
    denoteRegion Lambda.canonicalModel named fragmentOuter fragmentRelEnv
      (finishRegion (input.val.extractDiagramRaw payload.selection layout)
        fragmentContext layout.bodyContainer fragmentItems) := by
  let host := Classical.choice
    (Splice.siteView_complete input payload.selection.val.anchor)
  let hostContext := host.compilerLeaf.inheritedWires.extend
    payload.selection.val.anchor
  have selectedLocal : ∀ occurrence,
      occurrence ∈ ModalSoundness.selectedOccurrences input.val
          payload.selection →
        occurrence ∈ localOccurrences input.val
          payload.selection.val.anchor := by
    intro occurrence member
    rw [ModalSoundness.selectedOccurrences, List.mem_filter] at member
    exact member.1
  obtain ⟨hostItems, hostCompiled⟩ := compileOccurrencesWith?_complete
    (compileRegion? signature input.val host.compilerLeaf.fuel)
    hostContext host.compilerLeaf.binders
    (ModalSoundness.selectedOccurrences input.val payload.selection) (by
      intro occurrence member
      exact ModalSoundness.compileOccurrence_success_of_mem input.val
        (compileRegion? signature input.val host.compilerLeaf.fuel)
        hostContext host.compilerLeaf.binders
        host.compilerLeaf.itemsComputation (selectedLocal occurrence member))
  have hostExact : hostContext.Exact payload.selection.val.anchor :=
    host.compilerLeaf.wiresExact
  have fragmentVisible : ∀ wire, wire ∈ fragmentContext →
      (input.val.extractDiagramRaw payload.selection layout).Encloses
        ((input.val.extractDiagramRaw payload.selection layout).wires
          wire).scope layout.bodyContainer := by
    intro wire member
    apply (fragmentExact.mem_iff wire).1
    simp [WireContext.extend, member]
  have fragmentNodup : fragmentContext.Nodup :=
    (List.nodup_append.mp fragmentExact.nodup).1
  let indexMap := extractionHostIndexMap input payload.selection layout
    fragmentContext hostContext fragmentVisible hostExact
  let hostEnv := extendHostEnvironment indexMap fragmentOuter
  let binderWitness :=
    IterationSoundness.ExtractionBinderWitness.terminal input
      payload.selection layout fragmentBinders fragmentEnumeration
      host.compilerLeaf.binders host.compilerLeaf.bindersCover
  have relationInjective : ∀ arity,
      Function.Injective (@binderWitness.relationMap arity) :=
    terminalRelationMap_injective input payload.selection layout
      fragmentBinders host.compilerLeaf.binders fragmentEnumeration
      host.compilerLeaf.binderEnumeration host.compilerLeaf.bindersCover
  let hostRelEnv := extendRelEnv binderWitness.relationMap fragmentRelEnv
  have relationsAgree : RelEnv.Agrees binderWitness.relationMap
      fragmentRelEnv hostRelEnv :=
    extendRelEnv_agrees binderWitness.relationMap relationInjective
      fragmentRelEnv
  have hostDenotes : denoteItemSeq Lambda.canonicalModel named hostEnv
      hostRelEnv hostItems :=
    selected_items_true payload checked hostContext host.compilerLeaf.binders
      hostCompiled named hostEnv hostRelEnv
  have simulation :=
    IterationSoundness.extractionCompileTerminal_selected_denote input
      payload.selection layout Lambda.canonicalModel named
      fragmentFuel host.compilerLeaf.fuel fragmentContext hostContext fragmentBinders
      host.compilerLeaf.binders fragmentEnumeration
      host.compilerLeaf.binderEnumeration host.compilerLeaf.bindersCover
      fragmentExact hostExact fragmentItems hostItems fragmentCompiled
      hostCompiled
  have environmentsAgree := extractionEnvironmentsAgree_of_source input
    payload.selection layout fragmentContext hostContext fragmentVisible
    fragmentNodup hostExact fragmentOuter
  have renamed := simulation fragmentOuter hostEnv hostRelEnv
    environmentsAgree
    ((IterationSoundness.denoteRegion_mk_zero_iff Lambda.canonicalModel named
      hostEnv hostRelEnv hostItems).2 hostDenotes)
  exact (denoteRegion_renameRelations Lambda.canonicalModel named
    binderWitness.relationMap fragmentRelEnv hostRelEnv relationsAgree
    fragmentOuter
    (finishRegion (input.val.extractDiagramRaw payload.selection layout)
      fragmentContext layout.bodyContainer fragmentItems)).mp (by
        simpa [binderWitness] using renamed)

private theorem nested_zero_source_iff_host
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount}
    {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation
      payload.firstTerm payload.secondTerm)
    (decomposition : Decomposition signature input payload.selection)
    (hadmissible :
      (Splice.Decomposition.originalFragmentInput decomposition).Admissible)
    (sourceBoundary : List (Fin
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        wire).scope =
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hnested : (Splice.Decomposition.originalFragmentInput decomposition).site ≠
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hzero : (Splice.Decomposition.originalFragmentInput decomposition
      ).binderSpine.proxyCount = 0)
    (named : NamedEnv Lambda.Individual signature)
    (args : Fin
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Splice.Decomposition.originalFragmentInput decomposition)
        hadmissible sourceBoundary sourceRoot).val.boundary.length →
          Lambda.Individual) :
    denoteOpen Lambda.canonicalModel named
        (Splice.Input.compiledSpliceNestedSourceOfEmpty
          (Splice.Decomposition.originalFragmentInput decomposition)
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          hadmissible sourceBoundary sourceRoot hnested hzero) args ↔
      denoteOpen Lambda.canonicalModel named
        (Splice.Input.compiledSpliceNestedHostOpen
          (Splice.Decomposition.originalFragmentInput decomposition)
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          hadmissible sourceBoundary sourceRoot hnested) args := by
  let spliceInput := Splice.Decomposition.originalFragmentInput decomposition
  let layout := spliceInput.plugLayout
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let output := (Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    layout hadmissible sourceBoundary sourceRoot).elaborate
  let view := Splice.Input.compiledSpliceOutputOpenView spliceInput layout
    hadmissible sourceBoundary sourceRoot
  let outputLeaf := Splice.Input.compiledSpliceOutputNestedLeaf spliceInput
    layout hadmissible sourceBoundary sourceRoot hnested
  let localEq := WireContext.length_extend host.compilerLeaf.inheritedWires
    spliceInput.site
  let material := finishRoot spliceInput.pattern.val.exposedWires
    spliceInput.pattern.val.hiddenWires pattern.items
  let wireMap := fun index => Fin.cast localEq
    (layout.exposedWireRenaming hadmissible host index)
  let relationMap : RelationRenaming [] host.intrinsicPath.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming _
  let hostRelationMap : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let rawSplice := Region.spliceAt
    (exactScopeWires spliceInput.coalesceFrameRaw spliceInput.site).length
    (host.compilerLeaf.items.castWiresEq localEq) material wireMap relationMap
  let rawProjected := Region.mk
    (exactScopeWires spliceInput.coalesceFrameRaw spliceInput.site).length
    (host.compilerLeaf.items.castWiresEq localEq)
  let splice := (rawSplice.renameRelations hostRelationMap).renameWires
    rootWireEquiv
  let projected := (rawProjected.renameRelations hostRelationMap).renameWires
    rootWireEquiv
  let sourceBody := view.focus.context.fill splice
  let projectedBody := view.focus.context.fill projected
  let arityEq :
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput hadmissible
        sourceBoundary sourceRoot).val.boundary.length =
      (Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput layout
        hadmissible sourceBoundary sourceRoot).val.boundary.length := by
    simp [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Splice.Input.PlugLayout.coalescedOpenRoot,
      Splice.Input.PlugLayout.outputOpenRoot]
  have localEquiv : ∀ env relEnv,
      denoteRegion Lambda.canonicalModel named env relEnv splice ↔
        denoteRegion Lambda.canonicalModel named env relEnv projected := by
    intro env relEnv
    let hostRelations := RelEnv.pullback hostRelationMap relEnv
    have rawEquiv : denoteRegion Lambda.canonicalModel named
        (env ∘ rootWireEquiv) hostRelations rawSplice ↔
      denoteRegion Lambda.canonicalModel named
        (env ∘ rootWireEquiv) hostRelations rawProjected := by
      change denoteRegion Lambda.canonicalModel named
          (env ∘ rootWireEquiv) hostRelations rawSplice ↔
        ∃ hostLocal,
          denoteItemSeq Lambda.canonicalModel named
            (extendWireEnv (env ∘ rootWireEquiv) hostLocal) hostRelations
            (host.compilerLeaf.items.castWiresEq localEq)
      have spliceSem := Region.denote_spliceAt (patternRels := [])
        Lambda.canonicalModel named (env ∘ rootWireEquiv) hostRelations
        (PUnit.unit : RelEnv Lambda.Individual [])
        (exactScopeWires spliceInput.coalesceFrameRaw spliceInput.site).length
        (host.compilerLeaf.items.castWiresEq localEq) material wireMap
        relationMap (by intro arity relation; exact Fin.elim0 relation.index)
      constructor
      · intro sourceDenotes
        obtain ⟨hostLocal, hostDenotes, _⟩ := spliceSem.mp (by
          simpa [rawSplice] using sourceDenotes)
        exact ⟨hostLocal, hostDenotes⟩
      · rintro ⟨hostLocal, hostDenotes⟩
        have materialTrue := extracted_root_true payload checked
          decomposition.extraction.raw.layout
          (by simpa [spliceInput] using hzero) pattern named
          ((extendWireEnv (env ∘ rootWireEquiv) hostLocal) ∘ wireMap)
        apply spliceSem.mpr
        refine ⟨hostLocal, hostDenotes, ?_⟩
        simpa [spliceInput, material, pattern] using materialTrue
    have wireSource := denoteRegion_renameWires Lambda.canonicalModel named
      rootWireEquiv env relEnv (rawSplice.renameRelations hostRelationMap)
    have relSource := denoteRegion_renameRelations Lambda.canonicalModel named
        hostRelationMap hostRelations relEnv
        (RelEnv.pullback_agrees hostRelationMap relEnv)
        (env ∘ rootWireEquiv) rawSplice
    have relTarget := denoteRegion_renameRelations Lambda.canonicalModel named
      hostRelationMap hostRelations relEnv
      (RelEnv.pullback_agrees hostRelationMap relEnv)
      (env ∘ rootWireEquiv) rawProjected
    have wireTarget := denoteRegion_renameWires Lambda.canonicalModel named
      rootWireEquiv env relEnv
      (rawProjected.renameRelations hostRelationMap)
    exact wireSource.trans
      (relSource.trans (rawEquiv.trans relTarget.symm) |>.trans wireTarget.symm)
  have bodyEquiv : ∀ env,
      denoteRegion (relCtx := []) Lambda.canonicalModel named env PUnit.unit
          sourceBody ↔
        denoteRegion (relCtx := []) Lambda.canonicalModel named env PUnit.unit
          projectedBody := by
    intro env
    exact DiagramContext.fill_equiv view.focus.context splice projected
      Lambda.canonicalModel named env PUnit.unit localEquiv
  change denoteOpen Lambda.canonicalModel named
      ((Splice.replaceOpenBody output sourceBody).castArity arityEq.symm) args ↔
    denoteOpen Lambda.canonicalModel named
      ((Splice.replaceOpenBody output projectedBody).castArity arityEq.symm) args
  rw [denoteOpen_castArity, denoteOpen_castArity]
  constructor
  · apply Splice.denote_replaceOpenBody_mono
    intro env
    exact (bodyEquiv env).mp
  · apply Splice.denote_replaceOpenBody_mono
    intro env
    exact (bodyEquiv env).mpr

private theorem nested_nonzero_source_iff_host
    {signature : List Nat} {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount} {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation payload.firstTerm payload.secondTerm)
    (decomposition : Decomposition signature input payload.selection)
    (hadmissible :
      (Splice.Decomposition.originalFragmentInput decomposition).Admissible)
    (sourceBoundary : List (Fin
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        wire).scope =
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hnested : (Splice.Decomposition.originalFragmentInput decomposition).site ≠
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hnonempty : (Splice.Decomposition.originalFragmentInput decomposition
      ).binderSpine.proxyCount ≠ 0)
    (named : NamedEnv Lambda.Individual signature)
    (args : Fin (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (Splice.Decomposition.originalFragmentInput decomposition) hadmissible
      sourceBoundary sourceRoot).val.boundary.length → Lambda.Individual) :
    denoteOpen Lambda.canonicalModel named
        (Splice.Input.compiledSpliceNestedSourceOfNonempty
          (Splice.Decomposition.originalFragmentInput decomposition)
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          hadmissible sourceBoundary sourceRoot hnested hnonempty) args ↔
      denoteOpen Lambda.canonicalModel named
        (Splice.Input.compiledSpliceNestedHostOpen
          (Splice.Decomposition.originalFragmentInput decomposition)
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          hadmissible sourceBoundary sourceRoot hnested) args := by
  let spliceInput := Splice.Decomposition.originalFragmentInput decomposition
  let layout := spliceInput.plugLayout
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let output := (Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    layout hadmissible sourceBoundary sourceRoot).elaborate
  let view := Splice.Input.compiledSpliceOutputOpenView spliceInput layout
    hadmissible sourceBoundary sourceRoot
  let outputLeaf := Splice.Input.compiledSpliceOutputNestedLeaf spliceInput
    layout hadmissible sourceBoundary sourceRoot hnested
  let localEq := WireContext.length_extend host.compilerLeaf.inheritedWires
    spliceInput.site
  let material := finishRegion spliceInput.pattern.val.diagram
    pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
    pattern.leaf.items
  let wireMap := fun index => Fin.cast localEq
    (layout.bodyTerminalWireRenaming hadmissible host pattern.witness
      pattern.leaf hnonempty index)
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      host.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    layout.coalescedTerminalRelationRenaming hadmissible host.intrinsicPath
      host.compilerLeaf pattern.witness pattern.leaf hnonempty relation
  let hostRelationMap : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun {arity} relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
  let rootWireEquiv :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let rawSplice := Region.spliceAt
    (exactScopeWires spliceInput.coalesceFrameRaw spliceInput.site).length
    (host.compilerLeaf.items.castWiresEq localEq) material wireMap relationMap
  let rawProjected := Region.mk
    (exactScopeWires spliceInput.coalesceFrameRaw spliceInput.site).length
    (host.compilerLeaf.items.castWiresEq localEq)
  let splice := (rawSplice.renameRelations hostRelationMap).renameWires
    rootWireEquiv
  let projected := (rawProjected.renameRelations hostRelationMap).renameWires
    rootWireEquiv
  let sourceBody := view.focus.context.fill splice
  let projectedBody := view.focus.context.fill projected
  let arityEq :
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput hadmissible
        sourceBoundary sourceRoot).val.boundary.length =
      (Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput layout
        hadmissible sourceBoundary sourceRoot).val.boundary.length := by
    simp [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Splice.Input.PlugLayout.coalescedOpenRoot,
      Splice.Input.PlugLayout.outputOpenRoot]
  have localEquiv : ∀ env relEnv,
      denoteRegion Lambda.canonicalModel named env relEnv splice ↔
        denoteRegion Lambda.canonicalModel named env relEnv projected := by
    intro env relEnv
    let hostRelations := RelEnv.pullback hostRelationMap relEnv
    have rawEquiv : denoteRegion Lambda.canonicalModel named
        (env ∘ rootWireEquiv) hostRelations rawSplice ↔
      denoteRegion Lambda.canonicalModel named
        (env ∘ rootWireEquiv) hostRelations rawProjected := by
      change denoteRegion Lambda.canonicalModel named
          (env ∘ rootWireEquiv) hostRelations rawSplice ↔
        ∃ hostLocal, denoteItemSeq Lambda.canonicalModel named
          (extendWireEnv (env ∘ rootWireEquiv) hostLocal) hostRelations
          (host.compilerLeaf.items.castWiresEq localEq)
      let patternRelations := RelEnv.pullback relationMap hostRelations
      have spliceSem := Region.denote_spliceAt Lambda.canonicalModel named
        (env ∘ rootWireEquiv) hostRelations patternRelations
        (exactScopeWires spliceInput.coalesceFrameRaw spliceInput.site).length
        (host.compilerLeaf.items.castWiresEq localEq) material wireMap
        relationMap (RelEnv.pullback_agrees relationMap hostRelations)
      constructor
      · intro sourceDenotes
        obtain ⟨hostLocal, hostDenotes, _⟩ := spliceSem.mp (by
          simpa [rawSplice] using sourceDenotes)
        exact ⟨hostLocal, hostDenotes⟩
      · rintro ⟨hostLocal, hostDenotes⟩
        have materialTrue := extracted_terminal_true payload checked
          decomposition.extraction.raw.layout pattern.leaf.binders
          pattern.leaf.binderEnumeration pattern.leaf.inheritedWires
          pattern.leaf.wiresExact pattern.leaf.fuel
          pattern.leaf.itemsComputation named
          ((extendWireEnv (env ∘ rootWireEquiv) hostLocal) ∘ wireMap)
          patternRelations
        apply spliceSem.mpr
        refine ⟨hostLocal, hostDenotes, ?_⟩
        simpa [spliceInput, material, pattern] using materialTrue
    have wireSource := denoteRegion_renameWires Lambda.canonicalModel named
      rootWireEquiv env relEnv (rawSplice.renameRelations hostRelationMap)
    have relSource := denoteRegion_renameRelations Lambda.canonicalModel named
      hostRelationMap hostRelations relEnv
      (RelEnv.pullback_agrees hostRelationMap relEnv)
      (env ∘ rootWireEquiv) rawSplice
    have relTarget := denoteRegion_renameRelations Lambda.canonicalModel named
      hostRelationMap hostRelations relEnv
      (RelEnv.pullback_agrees hostRelationMap relEnv)
      (env ∘ rootWireEquiv) rawProjected
    have wireTarget := denoteRegion_renameWires Lambda.canonicalModel named
      rootWireEquiv env relEnv
      (rawProjected.renameRelations hostRelationMap)
    exact wireSource.trans
      (relSource.trans (rawEquiv.trans relTarget.symm) |>.trans wireTarget.symm)
  have bodyEquiv : ∀ env,
      denoteRegion (relCtx := []) Lambda.canonicalModel named env PUnit.unit
          sourceBody ↔
        denoteRegion (relCtx := []) Lambda.canonicalModel named env PUnit.unit
          projectedBody := by
    intro env
    exact DiagramContext.fill_equiv view.focus.context splice projected
      Lambda.canonicalModel named env PUnit.unit localEquiv
  change denoteOpen Lambda.canonicalModel named
      ((Splice.replaceOpenBody output sourceBody).castArity arityEq.symm) args ↔
    denoteOpen Lambda.canonicalModel named
      ((Splice.replaceOpenBody output projectedBody).castArity arityEq.symm) args
  rw [denoteOpen_castArity, denoteOpen_castArity]
  constructor
  · apply Splice.denote_replaceOpenBody_mono
    intro env
    exact (bodyEquiv env).mp
  · apply Splice.denote_replaceOpenBody_mono
    intro env
    exact (bodyEquiv env).mpr

private theorem root_zero_coalesced_iff_source
    {signature : List Nat} {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount} {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation payload.firstTerm payload.secondTerm)
    (decomposition : Decomposition signature input payload.selection)
    (hadmissible :
      (Splice.Decomposition.originalFragmentInput decomposition).Admissible)
    (sourceBoundary : List (Fin
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        wire).scope =
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hsite : (Splice.Decomposition.originalFragmentInput decomposition).site =
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hzero : (Splice.Decomposition.originalFragmentInput decomposition
      ).binderSpine.proxyCount = 0)
    (named : NamedEnv Lambda.Individual signature)
    (args : Fin (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (Splice.Decomposition.originalFragmentInput decomposition) hadmissible
      sourceBoundary sourceRoot).val.boundary.length → Lambda.Individual) :
    denoteOpen Lambda.canonicalModel named
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (Splice.Decomposition.originalFragmentInput decomposition)
          hadmissible sourceBoundary sourceRoot).elaborate args ↔
      denoteOpen Lambda.canonicalModel named
        (Splice.Input.compiledSpliceRootSourceOfEmpty
          (Splice.Decomposition.originalFragmentInput decomposition)
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          hadmissible sourceBoundary sourceRoot hsite hzero) args := by
  let spliceInput := Splice.Decomposition.originalFragmentInput decomposition
  have hsite' : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput] using hsite
  constructor
  · intro coalesced
    have host := (Splice.Input.compiledSpliceRootHostOfEmpty_denote_iff_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hzero Lambda.canonicalModel named args).mpr coalesced
    let rootHost := Splice.Input.compiledSpliceRootHostOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite' hzero
    let rootSource := Splice.Input.compiledSpliceRootSourceOfEmpty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite' hzero
    have host' : denoteOpen Lambda.canonicalModel named rootHost args := by
      simpa [rootHost] using host
    have hostToSource : denoteOpen Lambda.canonicalModel named rootHost args →
        denoteOpen Lambda.canonicalModel named rootSource args := by
      unfold rootHost rootSource
      unfold Splice.Input.compiledSpliceRootHostOfEmpty
        Splice.Input.compiledSpliceRootHostFromItems
        Splice.Input.compiledSpliceRootSourceOfEmpty
        Splice.Input.compiledSpliceRootSourceFromItems
      dsimp only
      apply Splice.denote_replaceOpenBody_mono
      intro environment hostBody
      unfold denoteRegion at hostBody ⊢
      obtain ⟨oldLocal, oldHost⟩ := hostBody
      let hostView := Splice.Input.compiledSpliceHostView spliceInput
        hadmissible
      let pattern := Splice.Input.compiledSpliceOpenRootItems
        spliceInput.pattern
      let outputWitness := Splice.Input.compiledSpliceOutputRootWitness
        spliceInput spliceInput.plugLayout hadmissible hsite'
      let outputLeaf := Splice.Input.compiledSpliceOutputRootLeaf spliceInput
        spliceInput.plugLayout hadmissible hsite'
      let castEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires
          (spliceInput.plugLayout.frameRegion spliceInput.site)
      let closedWire :=
        (spliceInput.plugLayout.siteCombinedWireEquivOfEmpty hadmissible
          hostView outputWitness outputLeaf hzero).trans
          (FiniteEquiv.finCast castEq).symm
      let rootExact : (outputLeaf.inheritedWires.extend
          (spliceInput.plugLayout.frameRegion spliceInput.site)).Exact
          spliceInput.plugLayout.plugRaw.root := by
        simpa [hsite'] using outputLeaf.wiresExact
      let outputRootEq : (Splice.Input.PlugLayout.outputOpenRoot spliceInput
          spliceInput.plugLayout sourceBoundary).rootWires.length =
          (Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).exposedWires.length +
          (Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).hiddenWires.length := by
        simp [OpenConcreteDiagram.rootWires]
      let outputTransport :=
        (Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
          spliceInput spliceInput.plugLayout hadmissible sourceBoundary
          sourceRoot (outputLeaf.inheritedWires.extend
            (spliceInput.plugLayout.frameRegion spliceInput.site))
          rootExact).trans (FiniteEquiv.finCast outputRootEq)
      let reindex := Splice.Input.PlugLayout.closedSourceToOpenRootReindex
        closedWire outputTransport
        (Splice.Input.PlugLayout.rootExposedWireEquiv spliceInput
          spliceInput.plugLayout sourceBoundary)
        (Splice.Input.PlugLayout.rootLocalWireEquivOfEmpty spliceInput
          spliceInput.plugLayout sourceBoundary hsite' hzero)
      let hostSeam := spliceInput.plugLayout.hostSeamPreparedWireOfEmpty
        hadmissible hostView
      let hostRel : RelationRenaming hostView.focus.holeRels
          outputWitness.toFocus.holeRels := fun {arity} relation =>
        spliceInput.plugLayout.hostRelationRenaming hostView.intrinsicPath
          hostView.compilerLeaf outputWitness outputLeaf relation
      let patternSeam :=
        spliceInput.plugLayout.patternRootSeamPreparedWireOfEmpty hadmissible
          hostView
      let patternRel : RelationRenaming []
          outputWitness.toFocus.holeRels :=
        Splice.Input.PlugLayout.emptyRelationRenaming
          outputWitness.toFocus.holeRels
      let hostPrepared :=
        (hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel
      let patternPrepared :=
        (pattern.items.renameWires patternSeam).renameRelations patternRel
      let fullOld := extendWireEnv environment oldLocal
      let outputRelations : RelEnv Lambda.Individual outputWitness.toFocus.holeRels :=
        PUnit.unit
      let hostRelations : RelEnv Lambda.Individual hostView.focus.holeRels :=
        RelEnv.pullback hostRel outputRelations
      have preparedHost := (denoteItemSeq_renameWires Lambda.canonicalModel named reindex
        fullOld outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mp (by
            simpa [hostView, pattern, outputWitness, outputLeaf, castEq,
              closedWire, rootExact, outputRootEq, outputTransport, reindex,
              hostSeam, hostRel, fullOld, outputRelations] using oldHost)
      have seamHost := (denoteItemSeq_renameRelations Lambda.canonicalModel named hostRel
        hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullOld ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mp preparedHost
      have rawHost := (denoteItemSeq_renameWires Lambda.canonicalModel named hostSeam
        (fullOld ∘ reindex) hostRelations hostView.compilerLeaf.items).mp
        seamHost
      have material := extracted_root_true payload checked
        decomposition.extraction.raw.layout
        (by simpa [spliceInput] using hzero) pattern named
        ((((fullOld ∘ reindex) ∘ hostSeam) ∘
          spliceInput.plugLayout.exposedWireRenaming hadmissible hostView))
      have material' : denoteRegion (relCtx := []) Lambda.canonicalModel named
          ((((fullOld ∘ reindex) ∘ hostSeam) ∘
            spliceInput.plugLayout.exposedWireRenaming hadmissible hostView))
          PUnit.unit
          (finishRoot spliceInput.pattern.val.exposedWires
            spliceInput.pattern.val.hiddenWires pattern.items) := by
        simpa [spliceInput] using material
      obtain ⟨materialLocal, materialItems⟩ := material'
      let hidden := (Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
        sourceBoundary).hiddenWires.length
      let extra := spliceInput.pattern.val.hiddenWires.length
      let oldHidden : Fin hidden → Lambda.Individual := fun index =>
        oldLocal (Fin.castAdd extra index)
      let newLocal : Fin (hidden + extra) → Lambda.Individual :=
        Fin.addCases oldHidden materialLocal
      let fullNew := extendWireEnv environment newLocal
      have hostEnvironmentEq :
          (fullNew ∘ reindex) ∘ hostSeam =
            (fullOld ∘ reindex) ∘ hostSeam := by
        funext index
        have factor :=
          Splice.Input.PlugLayout.closedSourceToOpenRootReindex_host_factor_empty
            spliceInput spliceInput.plugLayout hadmissible sourceBoundary
            sourceRoot hsite' hzero index
        change fullNew (reindex (hostSeam index)) =
          fullOld (reindex (hostSeam index))
        rw [factor]
        unfold Splice.Input.PlugLayout.rootHostOpenEmbedding
        exact congrFun
          (IterationSoundness.extendWireEnv_conjoinLeft_preserve environment oldLocal
            materialLocal) _
      have rawHostNew : denoteItemSeq Lambda.canonicalModel named
          (((fullNew ∘ reindex) ∘ hostSeam)) hostRelations
          hostView.compilerLeaf.items := by
        rw [hostEnvironmentEq]
        exact rawHost
      have seamHostNew := (denoteItemSeq_renameWires Lambda.canonicalModel named hostSeam
        (fullNew ∘ reindex) hostRelations hostView.compilerLeaf.items).mpr
        rawHostNew
      have preparedHostNew := (denoteItemSeq_renameRelations Lambda.canonicalModel named
        hostRel hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullNew ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mpr seamHostNew
      have finalHostNew := (denoteItemSeq_renameWires Lambda.canonicalModel named reindex
        fullNew outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mpr preparedHostNew
      refine ⟨newLocal, ?_⟩
      change denoteItemSeq Lambda.canonicalModel named fullNew outputRelations
        ((hostPrepared.append patternPrepared).renameWires reindex)
      rw [ItemSeq.renameWires_append, denoteItemSeq_append]
      refine ⟨?_, ?_⟩
      · simpa [hostView, outputWitness, outputLeaf, castEq, closedWire,
          rootExact, outputRootEq, outputTransport, reindex, hostSeam,
          hostRel, hostPrepared, hidden, extra, newLocal, fullNew,
          outputRelations] using finalHostNew
      · let patternLength : (spliceInput.pattern.val.exposedWires ++
            spliceInput.pattern.val.hiddenWires).length =
            spliceInput.pattern.val.exposedWires.length +
              spliceInput.pattern.val.hiddenWires.length := by simp
        let materialEnvironment := extendWireEnv
          (((fullOld ∘ reindex) ∘ hostSeam) ∘
            spliceInput.plugLayout.exposedWireRenaming hadmissible hostView)
          materialLocal
        let materialRelMap : RelationRenaming [] hostView.focus.holeRels :=
          Splice.Input.PlugLayout.emptyRelationRenaming
            hostView.focus.holeRels
        let materialRelations : RelEnv Lambda.Individual [] :=
          RelEnv.pullback materialRelMap hostRelations
        have rawPattern := (denoteItemSeq_renameWires Lambda.canonicalModel named
          (Fin.cast patternLength) materialEnvironment materialRelations
          pattern.items).mp (by
            simpa [pattern, hostView, materialEnvironment, materialRelMap,
              materialRelations, ItemSeq.castWiresEq_eq_renameWires] using
              materialItems)
        have patternEnvironmentEq :
            (fullNew ∘ reindex) ∘ patternSeam =
              materialEnvironment ∘ Fin.cast patternLength := by
          funext index
          let split := Fin.cast patternLength index
          have recover : Fin.cast patternLength.symm split = index := by
            apply Fin.ext
            rfl
          rw [← recover]
          refine Fin.addCases (fun exposed => ?_) (fun localIndex => ?_)
            split
          · have seamEq : patternSeam
                (Fin.cast patternLength.symm
                  (Fin.castAdd extra exposed)) =
              hostSeam
                (spliceInput.plugLayout.exposedWireRenaming hadmissible
                  hostView exposed) := by
              apply Fin.ext
              simp [patternSeam, hostSeam,
                Splice.Input.PlugLayout.patternRootSeamPreparedWireOfEmpty,
                Splice.Input.PlugLayout.hostSeamPreparedWireOfEmpty,
                Region.adjoinHostWire]
              rw [Fin.addCases_left]
              rfl
            simp only [Function.comp_apply]
            rw [seamEq]
            simp [materialEnvironment, extendWireEnv]
            exact congrFun hostEnvironmentEq
              (spliceInput.plugLayout.exposedWireRenaming hadmissible
                hostView exposed)
          · have factor := IterationSoundness.rootReindex_patternLocal_empty spliceInput
              spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
              hsite' hzero localIndex
            simp only [Function.comp_apply]
            rw [factor]
            have recoverLocal : Fin.cast patternLength
                (Fin.cast patternLength.symm
                  (Fin.natAdd spliceInput.pattern.val.exposedWires.length
                    localIndex)) =
                Fin.natAdd spliceInput.pattern.val.exposedWires.length
                  localIndex := by
              apply Fin.ext
              rfl
            rw [recoverLocal]
            dsimp only [fullNew, materialEnvironment, newLocal, hidden]
            simp only [extendWireEnv]
            have outerIndexEq :
                (Fin.natAdd
                    (Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
                      sourceBoundary).exposedWires.length
                    (Fin.natAdd hidden localIndex) :
                  Fin ((Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses + (hidden + extra))) =
                Fin.natAdd
                  (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses
                  (Fin.natAdd hidden localIndex) := by
              apply Fin.ext
              rfl
            rw [outerIndexEq, Fin.addCases_right, Fin.addCases_right,
              Fin.addCases_right]
        have rawPatternNew : denoteItemSeq Lambda.canonicalModel named
            (((fullNew ∘ reindex) ∘ patternSeam)) materialRelations
            pattern.items := by
          rw [patternEnvironmentEq]
          exact rawPattern
        have seamPattern := (denoteItemSeq_renameWires Lambda.canonicalModel named
          patternSeam (fullNew ∘ reindex) materialRelations
          pattern.items).mpr rawPatternNew
        have preparedPattern := (denoteItemSeq_renameRelations Lambda.canonicalModel named
          patternRel materialRelations outputRelations (by
            intro arity relation
            exact RelEnv.pullback_agrees patternRel outputRelations arity
              relation)
          (fullNew ∘ reindex)
          (pattern.items.renameWires patternSeam)).mpr seamPattern
        exact (denoteItemSeq_renameWires Lambda.canonicalModel named reindex fullNew
          outputRelations patternPrepared).mpr (by
            simpa [patternPrepared] using preparedPattern)
    exact (by
      simpa [rootSource, spliceInput, Subsingleton.elim hsite hsite'] using
        hostToSource host')
  · exact Splice.Input.compiledSpliceRootSourceOfEmpty_projects_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hzero Lambda.canonicalModel named args



private theorem root_nonzero_coalesced_iff_source
    {signature : List Nat} {input : CheckedDiagram signature}
    {region : Fin input.val.regionCount} {first second : Fin input.val.nodeCount}
    (payload : InconsistentCutPayload input region first second)
    (checked : Lambda.CheckedNormalSeparation payload.firstTerm payload.secondTerm)
    (decomposition : Decomposition signature input payload.selection)
    (hadmissible :
      (Splice.Decomposition.originalFragmentInput decomposition).Admissible)
    (sourceBoundary : List (Fin
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        wire).scope =
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hsite : (Splice.Decomposition.originalFragmentInput decomposition).site =
      (Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (hnonempty : (Splice.Decomposition.originalFragmentInput decomposition
      ).binderSpine.proxyCount ≠ 0)
    (named : NamedEnv Lambda.Individual signature)
    (args : Fin (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (Splice.Decomposition.originalFragmentInput decomposition) hadmissible
      sourceBoundary sourceRoot).val.boundary.length → Lambda.Individual) :
    denoteOpen Lambda.canonicalModel named
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (Splice.Decomposition.originalFragmentInput decomposition)
          hadmissible sourceBoundary sourceRoot).elaborate args ↔
      denoteOpen Lambda.canonicalModel named
        (Splice.Input.compiledSpliceRootSourceOfNonempty
          (Splice.Decomposition.originalFragmentInput decomposition)
          (Splice.Decomposition.originalFragmentInput decomposition).plugLayout
          hadmissible sourceBoundary sourceRoot hsite hnonempty) args := by
  let spliceInput := Splice.Decomposition.originalFragmentInput decomposition
  have hsite' : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput] using hsite
  constructor
  · intro coalesced
    have host := (Splice.Input.compiledSpliceRootHostOfNonempty_denote_iff_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hnonempty Lambda.canonicalModel named args).mpr coalesced
    let rootHost := Splice.Input.compiledSpliceRootHostOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite'
      hnonempty
    let rootSource := Splice.Input.compiledSpliceRootSourceOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hsite'
      hnonempty
    have host' : denoteOpen Lambda.canonicalModel named rootHost args := by
      simpa [rootHost] using host
    have hostToSource : denoteOpen Lambda.canonicalModel named rootHost args →
        denoteOpen Lambda.canonicalModel named rootSource args := by
      unfold rootHost rootSource
      unfold Splice.Input.compiledSpliceRootHostOfNonempty
        Splice.Input.compiledSpliceRootHostFromItems
        Splice.Input.compiledSpliceRootSourceOfNonempty
        Splice.Input.compiledSpliceRootSourceFromItems
      dsimp only
      apply Splice.denote_replaceOpenBody_mono
      intro environment hostBody
      unfold denoteRegion at hostBody ⊢
      obtain ⟨oldLocal, oldHost⟩ := hostBody
      let hostView := Splice.Input.compiledSpliceHostView spliceInput
        hadmissible
      let pattern := Splice.Input.compiledSpliceTerminalView spliceInput
        hnonempty
      let outputWitness := Splice.Input.compiledSpliceOutputRootWitness
        spliceInput spliceInput.plugLayout hadmissible hsite'
      let outputLeaf := Splice.Input.compiledSpliceOutputRootLeaf spliceInput
        spliceInput.plugLayout hadmissible hsite'
      let castEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires
          (spliceInput.plugLayout.frameRegion spliceInput.site)
      let closedWire :=
        (spliceInput.plugLayout.siteCombinedWireEquivOfNonempty hadmissible
          hostView outputWitness outputLeaf hnonempty).trans
          (FiniteEquiv.finCast castEq).symm
      let rootExact : (outputLeaf.inheritedWires.extend
          (spliceInput.plugLayout.frameRegion spliceInput.site)).Exact
          spliceInput.plugLayout.plugRaw.root := by
        simpa [hsite'] using outputLeaf.wiresExact
      let outputRootEq : (Splice.Input.PlugLayout.outputOpenRoot spliceInput
          spliceInput.plugLayout sourceBoundary).rootWires.length =
          (Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).exposedWires.length +
          (Splice.Input.PlugLayout.outputOpenRoot spliceInput
            spliceInput.plugLayout sourceBoundary).hiddenWires.length := by
        simp [OpenConcreteDiagram.rootWires]
      let outputTransport :=
        (Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
          spliceInput spliceInput.plugLayout hadmissible sourceBoundary
          sourceRoot (outputLeaf.inheritedWires.extend
            (spliceInput.plugLayout.frameRegion spliceInput.site))
          rootExact).trans (FiniteEquiv.finCast outputRootEq)
      let reindex := Splice.Input.PlugLayout.closedSourceToOpenRootReindex
        closedWire outputTransport
        (Splice.Input.PlugLayout.rootExposedWireEquiv spliceInput
          spliceInput.plugLayout sourceBoundary)
        (Splice.Input.PlugLayout.rootLocalWireEquivOfNonempty spliceInput
          spliceInput.plugLayout sourceBoundary hsite' hnonempty)
      let hostSeam := spliceInput.plugLayout.hostSeamPreparedWireOfNonempty
        hadmissible hostView
      let hostRel : RelationRenaming hostView.focus.holeRels
          outputWitness.toFocus.holeRels := fun {arity} relation =>
        spliceInput.plugLayout.hostRelationRenaming hostView.intrinsicPath
          hostView.compilerLeaf outputWitness outputLeaf relation
      let patternSeam :=
        spliceInput.plugLayout.patternSeamPreparedWireOfNonempty hadmissible
          hostView pattern.witness pattern.leaf hnonempty
      let patternRel : RelationRenaming pattern.witness.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun {arity} relation =>
        hostRel (spliceInput.plugLayout.coalescedTerminalRelationRenaming
          hadmissible hostView.intrinsicPath hostView.compilerLeaf
          pattern.witness pattern.leaf hnonempty relation)
      let hostPrepared :=
        (hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel
      let patternPrepared :=
        (pattern.leaf.items.renameWires patternSeam).renameRelations patternRel
      let fullOld := extendWireEnv environment oldLocal
      let outputRelations : RelEnv Lambda.Individual outputWitness.toFocus.holeRels :=
        PUnit.unit
      let hostRelations : RelEnv Lambda.Individual hostView.focus.holeRels :=
        RelEnv.pullback hostRel outputRelations
      have preparedHost := (denoteItemSeq_renameWires Lambda.canonicalModel named reindex
        fullOld outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mp (by
            simpa [hostView, pattern, outputWitness, outputLeaf, castEq,
              closedWire, rootExact, outputRootEq, outputTransport, reindex,
              hostSeam, hostRel, fullOld, outputRelations] using oldHost)
      have seamHost := (denoteItemSeq_renameRelations Lambda.canonicalModel named hostRel
        hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullOld ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mp preparedHost
      have rawHost := (denoteItemSeq_renameWires Lambda.canonicalModel named hostSeam
        (fullOld ∘ reindex) hostRelations hostView.compilerLeaf.items).mp
        seamHost
      let materialWire :=
        spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible hostView
          pattern.witness pattern.leaf hnonempty
      let materialRel : RelationRenaming pattern.witness.toFocus.holeRels
          hostView.focus.holeRels := fun {arity} relation =>
        spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
          hostView.intrinsicPath hostView.compilerLeaf pattern.witness
          pattern.leaf hnonempty relation
      let fragmentRelations := RelEnv.pullback materialRel hostRelations
      have material := extracted_terminal_true payload checked
        decomposition.extraction.raw.layout pattern.leaf.binders
        pattern.leaf.binderEnumeration pattern.leaf.inheritedWires
        pattern.leaf.wiresExact pattern.leaf.fuel
        pattern.leaf.itemsComputation named
        (((fullOld ∘ reindex) ∘ hostSeam) ∘ materialWire) fragmentRelations
      have material' : denoteRegion Lambda.canonicalModel named
          (((fullOld ∘ reindex) ∘ hostSeam) ∘ materialWire)
          fragmentRelations
          (finishRegion spliceInput.pattern.val.diagram
            pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
            pattern.leaf.items) := by
        simpa [spliceInput, materialWire, materialRel, fragmentRelations] using
          material
      obtain ⟨materialLocal, materialItems⟩ := material'
      let hidden := (Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
        sourceBoundary).hiddenWires.length
      let extra := (ConcreteElaboration.exactScopeWires
        spliceInput.pattern.val.diagram
        spliceInput.binderSpine.bodyContainer).length
      let oldHidden : Fin hidden → Lambda.Individual := fun index =>
        oldLocal (Fin.castAdd extra index)
      let newLocal : Fin (hidden + extra) → Lambda.Individual :=
        Fin.addCases oldHidden materialLocal
      let fullNew := extendWireEnv environment newLocal
      have hostEnvironmentEq :
          (fullNew ∘ reindex) ∘ hostSeam =
            (fullOld ∘ reindex) ∘ hostSeam := by
        funext index
        have factor :=
          Splice.Input.PlugLayout.closedSourceToOpenRootReindex_host_factor_nonempty
            spliceInput spliceInput.plugLayout hadmissible sourceBoundary
            sourceRoot hsite' hnonempty index
        change fullNew (reindex (hostSeam index)) =
          fullOld (reindex (hostSeam index))
        rw [factor]
        unfold Splice.Input.PlugLayout.rootHostOpenEmbedding
        exact congrFun
          (IterationSoundness.extendWireEnv_conjoinLeft_preserve environment oldLocal
            materialLocal) _
      have rawHostNew : denoteItemSeq Lambda.canonicalModel named
          (((fullNew ∘ reindex) ∘ hostSeam)) hostRelations
          hostView.compilerLeaf.items := by
        rw [hostEnvironmentEq]
        exact rawHost
      have seamHostNew := (denoteItemSeq_renameWires Lambda.canonicalModel named hostSeam
        (fullNew ∘ reindex) hostRelations hostView.compilerLeaf.items).mpr
        rawHostNew
      have preparedHostNew := (denoteItemSeq_renameRelations Lambda.canonicalModel named
        hostRel hostRelations outputRelations
        (RelEnv.pullback_agrees hostRel outputRelations)
        (fullNew ∘ reindex)
        (hostView.compilerLeaf.items.renameWires hostSeam)).mpr seamHostNew
      have finalHostNew := (denoteItemSeq_renameWires Lambda.canonicalModel named reindex
        fullNew outputRelations
        ((hostView.compilerLeaf.items.renameWires hostSeam).renameRelations
          hostRel)).mpr preparedHostNew
      refine ⟨newLocal, ?_⟩
      change denoteItemSeq Lambda.canonicalModel named fullNew outputRelations
        ((hostPrepared.append patternPrepared).renameWires reindex)
      rw [ItemSeq.renameWires_append, denoteItemSeq_append]
      refine ⟨?_, ?_⟩
      · simpa [hostView, outputWitness, outputLeaf, castEq, closedWire,
          rootExact, outputRootEq, outputTransport, reindex, hostSeam,
          hostRel, hostPrepared, hidden, extra, newLocal, fullNew,
          outputRelations] using
          finalHostNew
      · let patternLength := ConcreteElaboration.WireContext.length_extend
          pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
        let actualWire := spliceInput.plugLayout.bodyTerminalWireRenaming
          hadmissible hostView pattern.witness pattern.leaf hnonempty
        let actualRel : RelationRenaming pattern.witness.toFocus.holeRels
            hostView.focus.holeRels := fun {arity} relation =>
          spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
            hostView.intrinsicPath hostView.compilerLeaf pattern.witness
            pattern.leaf hnonempty relation
        let materialEnvironment := extendWireEnv
          ((((fullOld ∘ reindex) ∘ hostSeam) ∘ actualWire))
          materialLocal
        let materialRelations : RelEnv Lambda.Individual
            pattern.witness.toFocus.holeRels :=
          RelEnv.pullback actualRel hostRelations
        have rawPattern := (denoteItemSeq_renameWires Lambda.canonicalModel named
          (Fin.cast patternLength) materialEnvironment materialRelations
          pattern.leaf.items).mp (by
            simpa [pattern, hostView, actualWire, actualRel,
              materialEnvironment, materialRelations,
              ItemSeq.castWiresEq_eq_renameWires] using materialItems)
        have patternEnvironmentEq :
            (fullNew ∘ reindex) ∘ patternSeam =
              materialEnvironment ∘ Fin.cast patternLength := by
          funext index
          let split := Fin.cast patternLength index
          have recover : Fin.cast patternLength.symm split = index := by
            apply Fin.ext
            rfl
          rw [← recover]
          refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_)
            split
          · have seamEq : patternSeam
                (Fin.cast patternLength.symm
                  (Fin.castAdd extra inherited)) =
              hostSeam (actualWire inherited) := by
              apply Fin.ext
              simp [patternSeam, hostSeam, actualWire,
                Splice.Input.PlugLayout.patternSeamPreparedWireOfNonempty,
                Splice.Input.PlugLayout.hostSeamPreparedWireOfNonempty,
                Region.adjoinMaterialWire, Region.adjoinHostWire,
                extendWireRenaming]
              rw [Fin.addCases_left]
              rfl
            simp only [Function.comp_apply]
            rw [seamEq]
            simp [materialEnvironment, extendWireEnv]
            exact congrFun hostEnvironmentEq (actualWire inherited)
          · have factor := IterationSoundness.rootReindex_patternLocal_nonempty spliceInput
              spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
              hsite' hnonempty localIndex
            simp only [Function.comp_apply]
            rw [factor]
            have recoverLocal : Fin.cast patternLength
                (Fin.cast patternLength.symm
                  (Fin.natAdd pattern.leaf.inheritedWires.length
                    localIndex)) =
                Fin.natAdd pattern.leaf.inheritedWires.length localIndex := by
              apply Fin.ext
              rfl
            rw [recoverLocal]
            dsimp only [fullNew, materialEnvironment, newLocal, hidden]
            simp only [extendWireEnv]
            have outerIndexEq :
                (Fin.natAdd
                    (Splice.Input.PlugLayout.coalescedOpenRoot spliceInput
                      sourceBoundary).exposedWires.length
                    (Fin.natAdd hidden localIndex) :
                  Fin ((Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses + (hidden + extra))) =
                Fin.natAdd
                  (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
                    spliceInput hadmissible sourceBoundary sourceRoot
                      ).elaborate.externalClasses
                  (Fin.natAdd hidden localIndex) := by
              apply Fin.ext
              rfl
            rw [outerIndexEq, Fin.addCases_right, Fin.addCases_right,
              Fin.addCases_right]
        have rawPatternNew : denoteItemSeq Lambda.canonicalModel named
            (((fullNew ∘ reindex) ∘ patternSeam)) materialRelations
            pattern.leaf.items := by
          rw [patternEnvironmentEq]
          exact rawPattern
        have seamPattern := (denoteItemSeq_renameWires Lambda.canonicalModel named
          patternSeam (fullNew ∘ reindex) materialRelations
          pattern.leaf.items).mpr rawPatternNew
        have preparedPattern := (denoteItemSeq_renameRelations Lambda.canonicalModel named
          patternRel materialRelations outputRelations (by
            intro arity relation
            exact (RelEnv.pullback_agrees actualRel hostRelations arity
              relation).trans
              (RelEnv.pullback_agrees hostRel outputRelations arity
                (actualRel relation)))
          (fullNew ∘ reindex)
          (pattern.leaf.items.renameWires patternSeam)).mpr seamPattern
        exact (denoteItemSeq_renameWires Lambda.canonicalModel named reindex fullNew
          outputRelations patternPrepared).mpr (by
            simpa [patternPrepared] using preparedPattern)
    exact (by
      simpa [rootSource, spliceInput, Subsingleton.elim hsite hsite'] using
        hostToSource host')
  · exact Splice.Input.compiledSpliceRootSourceOfNonempty_projects_coalesced
      spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      hsite' hnonempty Lambda.canonicalModel named args
end VisualProof.Rule.InconsistentCutSoundness

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration
open InconsistentCutSoundness

private def inconsistentCutOperationalOpen
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireInterfaceTransport input selection))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    CheckedOpenDiagram signature :=
  ⟨realizes.rawResultOpen mapped,
    realizes.rawResultOpen_wellFormed sourceRoot htransport⟩

private def inconsistentCutOperationalIso
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireInterfaceTransport input selection))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    OpenConcreteIso
      (inconsistentCutOperationalOpen realizes boundary sourceRoot mapped
        htransport).val
      (realizes.rawResultOpen mapped) :=
  OpenConcreteIso.refl _

/-- Every successful inconsistent-cut-elimination receipt preserves canonical
semantics at every transported ordered boundary. -/
theorem applyInconsistentCutElim_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : CheckedDiagram signature)
    (region first second)
    (payload : InconsistentCutPayload input region first second)
    (receipt : StepReceipt input)
    (happly : applyInconsistentCutElim input region first second payload =
      .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.inconsistentCutElim region first second payload) receipt := by
  have hcertificate : Lambda.checkNormalSeparation payload.firstTerm
      payload.secondTerm payload.certificate = true := by
    unfold applyInconsistentCutElim at happly
    split at happly
    · assumption
    · contradiction
  let checked : Lambda.CheckedNormalSeparation payload.firstTerm
      payload.secondTerm := ⟨payload.certificate, hcertificate⟩
  have realizes := applyInconsistentCutElim_realizes input region first second
    payload receipt happly
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      inconsistentCutOperationalOpen realizes boundary sourceRoot mapped htransport)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      inconsistentCutOperationalIso realizes boundary sourceRoot mapped htransport)
  intro boundary sourceRoot mapped htransport valid args
  let rawMapped := realizes.targetBoundary mapped
  have hexpected :
      (removeWireInterfaceTransport input payload.selection).transportBoundary
        boundary = some rawMapped :=
    realizes.transportBoundary_expected htransport
  have rawRoot : ∀ wire, wire ∈ rawMapped →
      ((input.val.removeRaw payload.selection {}).wires wire).scope =
        (input.val.removeRaw payload.selection {}).root :=
    (removeWireInterfaceTransport input payload.selection)
      |>.transportBoundary_root_scoped sourceRoot hexpected
  let extraction := Classical.choose
    (Diagram.extractChecked_complete signature input payload.selection)
  let decomposition : Diagram.Decomposition signature input payload.selection := {
    frameDomains := {}
    frame := ⟨input.val.removeRaw payload.selection {},
      Diagram.ConcreteDiagram.removeRaw_wellFormed input payload.selection {}⟩
    frame_eq := rfl
    extraction := extraction
  }
  let spliceResult := Classical.choose
    (Diagram.Splice.Decomposition.reassemble_original_checked_complete
      decomposition)
  have hsplice : Diagram.Splice.Input.spliceChecked signature
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition) =
        .ok spliceResult :=
    Classical.choose_spec
      (Diagram.Splice.Decomposition.reassemble_original_checked_complete
        decomposition)
  have hcoalescedArity :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length = boundary.length := by
    change (rawMapped.map
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition).quotientWire).length =
        boundary.length
    simpa using
      (removeWireInterfaceTransport input payload.selection)
        |>.transportBoundary_length hexpected
  let commonArgs := args ∘ Fin.cast hcoalescedArity
  have hdirect :=
    Diagram.Splice.Decomposition.reassemble_original_source_open_denotation_iff_direct
      decomposition hsplice rawMapped rawRoot Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) commonArgs
  dsimp only at hdirect
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  have horigins : rawMapped.map decomposition.frameDomains.wires.origin =
      boundary := by
    simpa [decomposition, rawMapped] using
      removeWireInterfaceTransport_boundary_origins input payload.selection {}
        boundary rawMapped hexpected
  let sourceHostIso : Diagram.OpenConcreteIso source.asCheckedOpen.val
      (Diagram.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
        rawMapped rawRoot).val := {
    diagram := Diagram.ConcreteIso.refl input.val
    boundary := by
      change boundary.map (Diagram.ConcreteIso.refl input.val).wires =
        rawMapped.map decomposition.frameDomains.wires.origin
      simpa [Diagram.ConcreteIso.refl, Diagram.FiniteEquiv.refl] using
        horigins.symm
  }
  have hsourceHost := sourceHostIso.denote_iff source.asCheckedOpen.property
    (Diagram.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
      rawMapped rawRoot).property Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  let outputArityEq :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length =
      (Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length := by
    simp [Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Diagram.Splice.Input.PlugLayout.coalescedOpenRoot,
      Diagram.Splice.Input.PlugLayout.outputOpenRoot]
  let directArgs :=
    (commonArgs ∘ Fin.cast outputArityEq.symm) ∘ Fin.cast
      (Diagram.Splice.Decomposition.reassemble_original_output_open_iso
        decomposition rawMapped).boundary_length_eq.symm
  have hdirect' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen
            (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice rawMapped rawRoot) commonArgs ↔
        denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
            rawMapped rawRoot).elaborate directArgs := by
    simpa only [directArgs, outputArityEq] using hdirect
  have hdirectArgs : directArgs =
      (args ∘ Fin.cast sourceHostIso.boundary_length_eq.symm) := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  have hcompilerSource :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen
            (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice rawMapped rawRoot) commonArgs ↔
        source.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) args := by
    rw [hdirect', hdirectArgs]
    exact hsourceHost.symm
  let spliceInput :=
    Diagram.Splice.Decomposition.originalFragmentInput decomposition
  let hadmissible := (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1
  have hsourceFrame :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen spliceInput hsplice
            rawMapped rawRoot) commonArgs ↔
        denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
            hadmissible rawMapped rawRoot).elaborate commonArgs := by
    by_cases hsite : spliceInput.site = spliceInput.frame.val.root
    · by_cases hzero : spliceInput.binderSpine.proxyCount = 0
      · have equivalence :=
          InconsistentCutSoundness.root_zero_coalesced_iff_source payload
            checked decomposition hadmissible rawMapped rawRoot hsite hzero
            (Theory.interpretDefinitions context.definitions) commonArgs
        simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen, hsite,
          hzero, dite_true, spliceInput, hadmissible] using equivalence.symm
      · have equivalence :=
          InconsistentCutSoundness.root_nonzero_coalesced_iff_source payload
            checked decomposition hadmissible rawMapped rawRoot hsite hzero
            (Theory.interpretDefinitions context.definitions) commonArgs
        simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen, hsite,
          hzero, dite_true, dite_false, spliceInput, hadmissible] using
            equivalence.symm
    · by_cases hzero : spliceInput.binderSpine.proxyCount = 0
      · have sourceHost :=
          InconsistentCutSoundness.nested_zero_source_iff_host payload checked
            decomposition hadmissible rawMapped rawRoot hsite hzero
            (Theory.interpretDefinitions context.definitions) commonArgs
        have hostFrame :=
          Diagram.Splice.Input.compiledSpliceNestedHostOpen_denote_iff_coalesced
            spliceInput spliceInput.plugLayout hadmissible rawMapped rawRoot
            hsite Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions) commonArgs
        simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen, hsite,
          hzero, dite_false, dite_true, spliceInput, hadmissible] using
            sourceHost.trans hostFrame
      · have sourceHost :=
          InconsistentCutSoundness.nested_nonzero_source_iff_host payload
            checked decomposition hadmissible rawMapped rawRoot hsite hzero
            (Theory.interpretDefinitions context.definitions) commonArgs
        have hostFrame :=
          Diagram.Splice.Input.compiledSpliceNestedHostOpen_denote_iff_coalesced
            spliceInput spliceInput.plugLayout hadmissible rawMapped rawRoot
            hsite Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions) commonArgs
        simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen, hsite,
          hzero, dite_false, spliceInput, hadmissible] using
            sourceHost.trans hostFrame
  have hframeRawEq :
      Diagram.Splice.Decomposition.originalFrameOpenRaw decomposition
          rawMapped = realizes.rawResultOpen mapped := by
    rfl
  let frameIso : Diagram.OpenConcreteIso
      (Diagram.Splice.Input.PlugLayout.coalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        rawMapped)
      (realizes.rawResultOpen mapped) := by
    rw [← hframeRawEq]
    exact Diagram.Splice.Decomposition.originalCoalescedFrameOpenIso
      decomposition rawMapped
  have hframe := frameIso.denote_iff
    (Diagram.Splice.Input.PlugLayout.coalescedOpenRoot_wellFormed
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
      (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped rawRoot)
    (realizes.rawResultOpen_wellFormed sourceRoot htransport)
    Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) commonArgs
  let operationalIso := inconsistentCutOperationalIso realizes boundary sourceRoot
    mapped htransport
  let frameArgs := commonArgs ∘ Fin.cast frameIso.boundary_length_eq.symm
  let operationalArgs :=
    args ∘ Fin.cast (operationalIso.boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport)))
  have hopenArgs : frameArgs = operationalArgs := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  have hframe' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
            (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
            (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
            rawRoot).elaborate commonArgs ↔
        (inconsistentCutOperationalOpen realizes boundary sourceRoot mapped htransport).denote
            Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            operationalArgs := by
    rw [← hopenArgs]
    change denoteOpen Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
          (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
          rawRoot).elaborate commonArgs ↔
      denoteOpen Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        (inconsistentCutOperationalOpen realizes boundary sourceRoot mapped htransport).elaborate
        frameArgs
    exact hframe
  change DirectedEntailment .inconsistentCutElim orientation
    (source.denote Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) args)
    ((inconsistentCutOperationalOpen realizes boundary sourceRoot mapped htransport).denote
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        operationalArgs)
  unfold DirectedEntailment
  simp only [StepTag.semanticMode]
  exact hcompilerSource.symm.trans (hsourceFrame.trans hframe')


end VisualProof.Rule
