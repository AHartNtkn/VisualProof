import VisualProof.Rule.Structural.InconsistentCut
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

end VisualProof.Rule.InconsistentCutSoundness
