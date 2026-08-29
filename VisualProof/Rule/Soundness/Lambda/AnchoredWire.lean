import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.ContextReachability
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Rule.Lambda.AnchoredWire

namespace VisualProof.Rule.Lambda.AnchoredWire

open Diagram
open Theory

private theorem Values.exists_append
    (values : Values model (left ++ right)) :
    ∃ (leftValues : Values model left) (rightValues : Values model right),
      leftValues.append rightValues = values := by
  induction left with
  | nil => exact ⟨PUnit.unit, values, rfl⟩
  | cons signature rest induction =>
      rcases values with ⟨head, tail⟩
      rcases induction tail with ⟨leftValues, rightValues, equality⟩
      exact ⟨(head, leftValues), rightValues, congrArg (Prod.mk head) equality⟩

private def Values.singleton (model : Model) (value : model.Carrier) :
    Values model [Sig.iota] :=
  (value, PUnit.unit)

private theorem DiagramContext.denote_fill_iff
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (localIff : ∀ env : Values model holeWires,
      denoteRegion model env before ↔ denoteRegion model env after)
    (env : Values model outer) :
    denoteRegion model env (context.fill before) ↔
      denoteRegion model env (context.fill after) := by
  cases polarity : context.polarity with
  | positive =>
      constructor
      · have implication := context.denote_fill model before after
          (fun holeEnv => (localIff holeEnv).mp) env
        rw [polarity] at implication
        exact implication
      · have implication := context.denote_fill model after before
          (fun holeEnv => (localIff holeEnv).mpr) env
        rw [polarity] at implication
        exact implication
  | negative =>
      constructor
      · have implication := context.denote_fill model after before
          (fun holeEnv => (localIff holeEnv).mpr) env
        rw [polarity] at implication
        exact implication
      · have implication := context.denote_fill model before after
          (fun holeEnv => (localIff holeEnv).mp) env
        rw [polarity] at implication
        exact implication

private def closedValue (model : Model)
    (witness : ClosedInterfaceTerm arity) : model.Carrier :=
  model.eval (witness.closed.mapFree Empty.elim)
    (Fin.elim0 : Fin 0 → model.Carrier)

private theorem closedEvaluation (model : Model)
    (witness : ClosedInterfaceTerm arity)
    (environment : Fin arity → model.Carrier) :
    model.eval witness.term environment = closedValue model witness := by
  rw [witness.term_eq]
  let closedZero : VisualProof.Lambda.Term 0 (Fin 0) :=
    witness.closed.mapFree Empty.elim
  have evaluation := model.eval_mapFree
    (Fin.elim0 : Fin 0 → Fin arity) closedZero environment
  have emptyMap :
      (Fin.elim0 : Fin 0 → Fin arity) ∘
          (Empty.elim : Empty → Fin 0) =
        (Empty.elim : Empty → Fin arity) := by
    funext impossible
    exact Empty.elim impossible
  rw [VisualProof.Lambda.Term.mapFree_comp, emptyMap] at evaluation
  have emptyEnvironment :
      environment ∘ (Fin.elim0 : Fin 0 → Fin arity) =
        (Fin.elim0 : Fin 0 → model.Carrier) := by
    funext impossible
    exact Fin.elim0 impossible
  exact evaluation.trans (congrArg (model.eval closedZero) emptyEnvironment)

private theorem Pin.sound_iff
    {outer : List Sig} {source target : Region outer}
    (description : Pin.Description source target)
    (model : Model) (environment : Values model outer) :
    denoteRegion model environment source ↔
      denoteRegion model environment target := by
  have filled := DiagramContext.denote_fill_iff description.context
    (.mk description.locals description.items)
    (.mk description.locals
      (description.items.append (.cons
        (.identity description.signature 1 (fun _ => description.wire)) .nil)))
    (model := model) (fun siteEnv => by
      simp only [denoteRegion_mk]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        refine ⟨localEnv, (denoteItemSeq_append model
          (siteEnv.append localEnv) description.items _).mpr
            ⟨itemsDenote, ?_⟩⟩
        exact ⟨denoteItem_unary_identity model (siteEnv.append localEnv)
          description.wire, trivial⟩
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, (denoteItemSeq_append model
          (siteEnv.append localEnv) description.items _).mp itemsDenote |>.1⟩)
    environment
  simpa only [description.source_eq, description.target_eq] using filled

private theorem CompletionPlan.sound_iff
    {outer : List Sig} {source target : Region outer}
    (plan : CompletionPlan maximum source target)
    (model : Model) (environment : Values model outer) :
    denoteRegion model environment source ↔
      denoteRegion model environment target := by
  induction plan with
  | done => exact Iff.rfl
  | step pin _ _ rest induction =>
      exact (Pin.sound_iff pin model environment).trans induction

private theorem Split.Primary.renamedEnvironment_outer
    {outer : List Sig} {source : Region outer}
    (primary : Split.Primary source) (model : Model)
    (outerEnv : Values model primary.siteWires)
    (localEnv : Values model primary.locals) :
    ∃ targetLocal : Values model (primary.locals ++ [.iota]),
      outerEnv.append targetLocal =
        Values.rename
          (WireSever.collapseLocal primary.siteWires primary.locals
            primary.anchor)
          (outerEnv.append localEnv) := by
  let collapse := WireSever.collapseLocal primary.siteWires primary.locals
    primary.anchor
  let renamed := Values.rename collapse (outerEnv.append localEnv)
  let targetLocal : Values model (primary.locals ++ [.iota]) :=
    Values.ofLookup fun wire => renamed.lookup
      (Var.appendRight primary.siteWires wire)
  refine ⟨targetLocal, ?_⟩
  apply Values.ext
  intro signature wire
  refine Var.appendCases (left := primary.siteWires)
    (right := primary.locals ++ [.iota])
    (motive := fun wire =>
      (outerEnv.append targetLocal).lookup wire = renamed.lookup wire)
    (fun inherited => by
      simp [targetLocal, renamed, collapse, WireSever.collapseLocal])
    (fun localWire => by simp [targetLocal]) wire

private theorem Split.Primary.sound_iff
    {outer : List Sig} {source : Region outer}
    (primary : Split.Primary source)
    (model : Model) (outerEnv : Values model primary.siteWires)
    (anchorValue : ∀ localEnv : Values model primary.locals,
      (outerEnv.append localEnv).lookup primary.anchor =
        closedValue model primary.witness) :
    denoteRegion model outerEnv primary.sourceBody ↔
      denoteRegion model outerEnv primary.targetBody := by
  let collapse := WireSever.collapseLocal primary.siteWires primary.locals
    primary.anchor
  let separated := primary.away.partitionOutput collapse primary.partition
  constructor
  · rintro ⟨localEnv, awayDenotes⟩
    obtain ⟨targetLocal, environmentEq⟩ :=
      Split.Primary.renamedEnvironment_outer primary model outerEnv localEnv
    refine ⟨targetLocal, ?_⟩
    rw [environmentEq]
    constructor
    · simp only [denoteItem_term, Values.lookup_rename]
      rw [closedEvaluation]
      rw [show collapse primary.fresh = primary.anchor by
        exact WireSever.collapseLocal_last primary.anchor]
      exact anchorValue localEnv
    · have renamed := denoteItemSeq_renameWires model collapse
          (outerEnv.append localEnv) separated
      apply renamed.mp
      simpa only [separated, collapse,
        ItemSeq.partitionOutput_renameWires] using awayDenotes
  · rintro ⟨targetLocal, targetDenotes⟩
    rcases Values.exists_append (left := primary.locals)
      (right := [.iota]) targetLocal with
      ⟨localEnv, freshEnv, targetLocalEq⟩
    rcases freshEnv with ⟨freshValue, unitValue⟩
    cases unitValue
    subst targetLocal
    rcases targetDenotes with ⟨duplicateDenotes, separatedDenotes⟩
    let oldEnv := outerEnv.append localEnv
    let targetEnv := outerEnv.append
      (localEnv.append (Values.singleton model freshValue))
    have duplicateValue : freshValue = closedValue model primary.witness := by
      simp only [denoteItem_term] at duplicateDenotes
      have outputLookup : targetEnv.lookup primary.fresh = freshValue := by
        simp only [targetEnv, Split.Primary.fresh,
          Values.lookup_append_right, Values.singleton]
        rfl
      have evaluated := closedEvaluation model primary.witness
        (fun slot => targetEnv.lookup (primary.retain (primary.ports slot)))
      exact outputLookup ▸ duplicateDenotes.trans evaluated
    have freshEqualsAnchor : freshValue = oldEnv.lookup primary.anchor := by
      exact duplicateValue.trans (anchorValue localEnv).symm
    have environmentEq : targetEnv = Values.rename collapse oldEnv := by
      apply Values.ext
      intro signature wire
      refine Var.appendCases (left := primary.siteWires)
        (right := primary.locals ++ [.iota])
        (motive := fun wire => targetEnv.lookup wire =
          (Values.rename collapse oldEnv).lookup wire)
        (fun inherited => by
          simp [targetEnv, oldEnv, collapse, WireSever.collapseLocal])
        (fun localWire => by
          refine Var.appendCases (left := primary.locals) (right := [.iota])
            (motive := fun localWire => targetEnv.lookup
              (Var.appendRight primary.siteWires localWire) =
              (Values.rename collapse oldEnv).lookup
                (Var.appendRight primary.siteWires localWire))
            (fun retained => by
              simp [targetEnv, oldEnv, collapse, WireSever.collapseLocal])
            (fun fresh => by
              cases fresh with
              | here =>
                  simpa [targetEnv, oldEnv, collapse,
                    WireSever.collapseLocal] using freshEqualsAnchor
              | there tail => exact nomatch tail) localWire) wire
    refine ⟨localEnv, ?_⟩
    have renamed := denoteItemSeq_renameWires model collapse oldEnv separated
    have separatedUnder : denoteItemSeq model
        (Values.rename collapse oldEnv) separated := by
      rw [← environmentEq]
      exact separatedDenotes
    simpa only [separated, collapse,
      ItemSeq.partitionOutput_renameWires] using renamed.mpr separatedUnder

private theorem closedValuesEqual
    (model : Model)
    {leftArity rightArity : Nat}
    (left : ClosedInterfaceTerm leftArity)
    (right : ClosedInterfaceTerm rightArity)
    (conversion : VisualProof.Lambda.BetaEta left.closed right.closed) :
    closedValue model left = closedValue model right := by
  exact model.betaEta_sound (conversion.mapFree Empty.elim)

private theorem Contract.Primary.collapsedEnvironment
    {outer : List Sig} {source : Region outer}
    (primary : Contract.Primary source) (model : Model)
    (outerEnv : Values model primary.siteWires)
    (localEnv : Values model primary.locals)
    (dropValue : model.Carrier)
    (dropEqualsSurvivor : dropValue =
      (outerEnv.append localEnv).lookup primary.survivorOutput) :
    Values.rename primary.collapse (outerEnv.append localEnv) =
      outerEnv.append (localEnv.append (Values.singleton model dropValue)) := by
  apply Values.ext
  intro signature wire
  refine Var.appendCases (left := primary.siteWires)
    (right := primary.locals ++ [.iota])
    (motive := fun wire =>
      (Values.rename primary.collapse (outerEnv.append localEnv)).lookup wire =
        (outerEnv.append (localEnv.append
          (Values.singleton model dropValue))).lookup wire)
    (fun inherited => by
      simp [Contract.Primary.collapse, WireSever.collapseLocal])
    (fun localWire => by
      refine Var.appendCases (left := primary.locals) (right := [.iota])
        (motive := fun localWire =>
          (Values.rename primary.collapse
            (outerEnv.append localEnv)).lookup
              (Var.appendRight primary.siteWires localWire) =
            (outerEnv.append (localEnv.append
              (Values.singleton model dropValue))).lookup
              (Var.appendRight primary.siteWires localWire))
        (fun retained => by
          simp [Contract.Primary.collapse, WireSever.collapseLocal])
        (fun fresh => by
          cases fresh with
          | here =>
              simpa [Contract.Primary.collapse, WireSever.collapseLocal,
                Values.singleton] using dropEqualsSurvivor.symm
          | there tail => exact nomatch tail) localWire) wire

private theorem Contract.Primary.sound_iff
    {outer : List Sig} {source : Region outer}
    (primary : Contract.Primary source)
    (survivor : ClosedInterfaceTerm survivorArity)
    (conversion : VisualProof.Lambda.BetaEta
      primary.redundant.closed survivor.closed)
    (model : Model) (outerEnv : Values model primary.siteWires)
    (survivorValue : ∀ localEnv : Values model primary.locals,
      (outerEnv.append localEnv).lookup primary.survivorOutput =
        closedValue model survivor) :
    denoteRegion model outerEnv primary.sourceBody ↔
      denoteRegion model outerEnv primary.targetBody := by
  constructor
  · rintro ⟨expandedLocal, redundantDenotes, awayDenotes⟩
    rcases Values.exists_append (left := primary.locals)
      (right := [.iota]) expandedLocal with
      ⟨localEnv, dropEnv, expandedEq⟩
    rcases dropEnv with ⟨dropValue, unitValue⟩
    cases unitValue
    subst expandedLocal
    have dropEqualsClosed : dropValue =
        closedValue model primary.redundant := by
      simp only [denoteItem_term] at redundantDenotes
      have outputLookup :
          (outerEnv.append (localEnv.append
            (Values.singleton model dropValue))).lookup primary.drop =
            dropValue := by
        simp only [Contract.Primary.drop, Values.lookup_append_right,
          Values.singleton]
        rfl
      exact outputLookup ▸ redundantDenotes.trans
        (closedEvaluation model primary.redundant _)
    have dropEqualsSurvivor : dropValue =
        (outerEnv.append localEnv).lookup primary.survivorOutput :=
      dropEqualsClosed.trans ((closedValuesEqual model primary.redundant
        survivor conversion).trans (survivorValue localEnv).symm)
    refine ⟨localEnv, ?_⟩
    have renamed := denoteItemSeq_renameWires model primary.collapse
      (outerEnv.append localEnv) primary.away
    apply renamed.mpr
    rw [Contract.Primary.collapsedEnvironment primary model outerEnv localEnv
      dropValue dropEqualsSurvivor]
    exact awayDenotes
  · rintro ⟨localEnv, targetDenotes⟩
    let survivorOutputValue :=
      (outerEnv.append localEnv).lookup primary.survivorOutput
    refine ⟨localEnv.append
      (Values.singleton model survivorOutputValue), ?_⟩
    constructor
    · simp only [denoteItem_term]
      change (outerEnv.append (localEnv.append
          (Values.singleton model survivorOutputValue))).lookup primary.drop = _
      have outputLookup :
          (outerEnv.append (localEnv.append
            (Values.singleton model survivorOutputValue))).lookup
              primary.drop = survivorOutputValue := by
        simp only [Contract.Primary.drop, Values.lookup_append_right,
          Values.singleton]
        rfl
      rw [outputLookup, closedEvaluation]
      exact (survivorValue localEnv).trans
        (closedValuesEqual model primary.redundant survivor conversion).symm
    · have renamed := denoteItemSeq_renameWires model primary.collapse
          (outerEnv.append localEnv) primary.away
      have expanded := renamed.mp targetDenotes
      rw [Contract.Primary.collapsedEnvironment primary model outerEnv localEnv
        survivorOutputValue rfl] at expanded
      exact expanded

private theorem Witness.outputValue
    {outer : List Sig} {selected : Region outer}
    (description : Witness.Description selected)
    (model : Model) (environment : Values model outer)
    (denotes : denoteRegion model environment selected) :
    environment.lookup description.output =
      closedValue model description.witness := by
  rw [description.selected_eq] at denotes
  rcases denotes with ⟨localEnv, itemsDenote⟩
  rcases (denoteItemSeq_frame model (environment.append localEnv)
    description.before description.after _).mp itemsDenote with
    ⟨_, termDenotes, _⟩
  simp only [denoteItem_term] at termDenotes
  have outputLookup : (environment.append localEnv).lookup
      (description.output.appendLeft description.locals) =
        environment.lookup description.output := by simp
  exact outputLookup ▸ termDenotes.trans
    (closedEvaluation model description.witness _)

private theorem closedValue_cast
    (model : Model) {leftArity rightArity : Nat}
    (sameArity : leftArity = rightArity)
    (left : ClosedInterfaceTerm leftArity)
    (right : ClosedInterfaceTerm rightArity)
    (same : left = sameArity ▸ right) :
    closedValue model left = closedValue model right := by
  subst rightArity
  subst left
  rfl

private theorem Split.Description.factor_sound_iff
    (description : Split.Description source)
    (model : Model)
    (environment : Values model description.occurrence.interface.external) :
    denoteRegion model environment
        (description.occurrence.targetBody description.occurrence.before) ↔
      denoteRegion model environment
        (description.occurrence.targetBody description.primary.targetRoot) := by
  let occurrence := description.occurrence
  let witness := description.witness
  let primary := description.primary
  have sameClosedValue : closedValue model primary.witness =
      closedValue model witness.witness :=
    closedValue_cast model description.sameArity primary.witness
      witness.witness description.sameWitness
  unfold NestedOccurrence.targetBody nestedBody
  apply DiagramContext.denote_fill_iff
  intro ancestorEnv
  rw [Region.denote_adjoinAt, Region.denote_adjoinAt]
  constructor
  · rintro ⟨anchorLocalEnv, _, combinedDenotes⟩
    refine ⟨anchorLocalEnv, trivial, ?_⟩
    rw [Region.denote_conjoin] at combinedDenotes ⊢
    rcases combinedDenotes with ⟨selectedDenotes, descendantDenotes⟩
    refine ⟨selectedDenotes, ?_⟩
    let anchorEnv := ancestorEnv.append anchorLocalEnv
    have witnessValue := Witness.outputValue witness model anchorEnv
      selectedDenotes
    have descendantIff := occurrence.descendant.fill_equiv_of_reachable
      occurrence.before primary.targetRoot model anchorEnv
      (fun holeEnv descendantReachable => by
        have primaryIff := primary.context.fill_equiv_of_reachable
          primary.sourceBody primary.targetBody model holeEnv
          (fun siteEnv primaryReachable => by
            apply Split.Primary.sound_iff primary model siteEnv
            intro localEnv
            rw [description.anchorVisible]
            have primaryOuter := primaryReachable.outerWire
            have descendantOuter := descendantReachable.outerWire
            have primaryLookup := congrArg
              (fun values => values.lookup
                (occurrence.descendant.outerWire witness.output)) primaryOuter
            have descendantLookup := congrArg
              (fun values => values.lookup witness.output) descendantOuter
            have primaryLookup' : siteEnv.lookup
                (primary.context.outerWire
                  (occurrence.descendant.outerWire witness.output)) =
              holeEnv.lookup
                (occurrence.descendant.outerWire witness.output) := by
              simpa only [Values.lookup_rename] using primaryLookup
            have descendantLookup' : holeEnv.lookup
                (occurrence.descendant.outerWire witness.output) =
              anchorEnv.lookup witness.output := by
              simpa only [Values.lookup_rename] using descendantLookup
            change (siteEnv.append localEnv).lookup
                ((primary.context.outerWire
                  (occurrence.descendant.outerWire witness.output)).appendLeft
                    primary.locals) = closedValue model primary.witness
            exact (Values.lookup_append_left siteEnv localEnv _).trans
              (primaryLookup'.trans (descendantLookup'.trans
                (witnessValue.trans sameClosedValue.symm))))
        have sourceEq : primary.context.fill primary.sourceBody =
            occurrence.before := primary.source_eq
        rw [sourceEq] at primaryIff
        exact primaryIff)
    exact descendantIff.mp descendantDenotes
  · rintro ⟨anchorLocalEnv, _, combinedDenotes⟩
    refine ⟨anchorLocalEnv, trivial, ?_⟩
    rw [Region.denote_conjoin] at combinedDenotes ⊢
    rcases combinedDenotes with ⟨selectedDenotes, descendantDenotes⟩
    refine ⟨selectedDenotes, ?_⟩
    let anchorEnv := ancestorEnv.append anchorLocalEnv
    have witnessValue := Witness.outputValue witness model anchorEnv
      selectedDenotes
    have descendantIff := occurrence.descendant.fill_equiv_of_reachable
      occurrence.before primary.targetRoot model anchorEnv
      (fun holeEnv descendantReachable => by
        have primaryIff := primary.context.fill_equiv_of_reachable
          primary.sourceBody primary.targetBody model holeEnv
          (fun siteEnv primaryReachable => by
            apply Split.Primary.sound_iff primary model siteEnv
            intro localEnv
            rw [description.anchorVisible]
            have primaryOuter := primaryReachable.outerWire
            have descendantOuter := descendantReachable.outerWire
            have primaryLookup := congrArg
              (fun values => values.lookup
                (occurrence.descendant.outerWire witness.output)) primaryOuter
            have descendantLookup := congrArg
              (fun values => values.lookup witness.output) descendantOuter
            have primaryLookup' : siteEnv.lookup
                (primary.context.outerWire
                  (occurrence.descendant.outerWire witness.output)) =
              holeEnv.lookup
                (occurrence.descendant.outerWire witness.output) := by
              simpa only [Values.lookup_rename] using primaryLookup
            have descendantLookup' : holeEnv.lookup
                (occurrence.descendant.outerWire witness.output) =
              anchorEnv.lookup witness.output := by
              simpa only [Values.lookup_rename] using descendantLookup
            change (siteEnv.append localEnv).lookup
                ((primary.context.outerWire
                  (occurrence.descendant.outerWire witness.output)).appendLeft
                    primary.locals) = closedValue model primary.witness
            exact (Values.lookup_append_left siteEnv localEnv _).trans
              (primaryLookup'.trans (descendantLookup'.trans
                (witnessValue.trans sameClosedValue.symm))))
        have sourceEq : primary.context.fill primary.sourceBody =
            occurrence.before := primary.source_eq
        rw [sourceEq] at primaryIff
        exact primaryIff)
    exact descendantIff.mpr descendantDenotes

private theorem Contract.Description.factor_sound_iff
    (description : Contract.Description source)
    (model : Model)
    (environment : Values model description.occurrence.interface.external) :
    denoteRegion model environment
        (description.occurrence.targetBody description.occurrence.before) ↔
      denoteRegion model environment
        (description.occurrence.targetBody description.primary.targetRoot) := by
  let occurrence := description.occurrence
  let survivor := description.survivor
  let primary := description.primary
  unfold NestedOccurrence.targetBody nestedBody
  apply DiagramContext.denote_fill_iff
  intro ancestorEnv
  rw [Region.denote_adjoinAt, Region.denote_adjoinAt]
  constructor
  · rintro ⟨anchorLocalEnv, _, combinedDenotes⟩
    refine ⟨anchorLocalEnv, trivial, ?_⟩
    rw [Region.denote_conjoin] at combinedDenotes ⊢
    rcases combinedDenotes with ⟨selectedDenotes, descendantDenotes⟩
    refine ⟨selectedDenotes, ?_⟩
    let anchorEnv := ancestorEnv.append anchorLocalEnv
    have survivorValueAtAnchor := Witness.outputValue survivor model anchorEnv
      selectedDenotes
    have descendantIff := occurrence.descendant.fill_equiv_of_reachable
      occurrence.before primary.targetRoot model anchorEnv
      (fun holeEnv descendantReachable => by
        have primaryIff := primary.context.fill_equiv_of_reachable
          primary.sourceBody primary.targetBody model holeEnv
          (fun siteEnv primaryReachable => by
            apply Contract.Primary.sound_iff primary survivor.witness
              description.conversion model siteEnv
            intro localEnv
            rw [description.sameSurvivorWire]
            have primaryOuter := primaryReachable.outerWire
            have descendantOuter := descendantReachable.outerWire
            have primaryLookup := congrArg
              (fun values => values.lookup
                (occurrence.descendant.outerWire survivor.output)) primaryOuter
            have descendantLookup := congrArg
              (fun values => values.lookup survivor.output) descendantOuter
            have primaryLookup' : siteEnv.lookup
                (primary.context.outerWire
                  (occurrence.descendant.outerWire survivor.output)) =
              holeEnv.lookup
                (occurrence.descendant.outerWire survivor.output) := by
              simpa only [Values.lookup_rename] using primaryLookup
            have descendantLookup' : holeEnv.lookup
                (occurrence.descendant.outerWire survivor.output) =
              anchorEnv.lookup survivor.output := by
              simpa only [Values.lookup_rename] using descendantLookup
            change (siteEnv.append localEnv).lookup
                ((primary.context.outerWire
                  (occurrence.descendant.outerWire survivor.output)).appendLeft
                    primary.locals) = closedValue model survivor.witness
            exact (Values.lookup_append_left siteEnv localEnv _).trans
              (primaryLookup'.trans (descendantLookup'.trans
                survivorValueAtAnchor)))
        have sourceEq : primary.context.fill primary.sourceBody =
            occurrence.before := primary.source_eq
        rw [sourceEq] at primaryIff
        exact primaryIff)
    exact descendantIff.mp descendantDenotes
  · rintro ⟨anchorLocalEnv, _, combinedDenotes⟩
    refine ⟨anchorLocalEnv, trivial, ?_⟩
    rw [Region.denote_conjoin] at combinedDenotes ⊢
    rcases combinedDenotes with ⟨selectedDenotes, descendantDenotes⟩
    refine ⟨selectedDenotes, ?_⟩
    let anchorEnv := ancestorEnv.append anchorLocalEnv
    have survivorValueAtAnchor := Witness.outputValue survivor model anchorEnv
      selectedDenotes
    have descendantIff := occurrence.descendant.fill_equiv_of_reachable
      occurrence.before primary.targetRoot model anchorEnv
      (fun holeEnv descendantReachable => by
        have primaryIff := primary.context.fill_equiv_of_reachable
          primary.sourceBody primary.targetBody model holeEnv
          (fun siteEnv primaryReachable => by
            apply Contract.Primary.sound_iff primary survivor.witness
              description.conversion model siteEnv
            intro localEnv
            rw [description.sameSurvivorWire]
            have primaryOuter := primaryReachable.outerWire
            have descendantOuter := descendantReachable.outerWire
            have primaryLookup := congrArg
              (fun values => values.lookup
                (occurrence.descendant.outerWire survivor.output)) primaryOuter
            have descendantLookup := congrArg
              (fun values => values.lookup survivor.output) descendantOuter
            have primaryLookup' : siteEnv.lookup
                (primary.context.outerWire
                  (occurrence.descendant.outerWire survivor.output)) =
              holeEnv.lookup
                (occurrence.descendant.outerWire survivor.output) := by
              simpa only [Values.lookup_rename] using primaryLookup
            have descendantLookup' : holeEnv.lookup
                (occurrence.descendant.outerWire survivor.output) =
              anchorEnv.lookup survivor.output := by
              simpa only [Values.lookup_rename] using descendantLookup
            change (siteEnv.append localEnv).lookup
                ((primary.context.outerWire
                  (occurrence.descendant.outerWire survivor.output)).appendLeft
                    primary.locals) = closedValue model survivor.witness
            exact (Values.lookup_append_left siteEnv localEnv _).trans
              (primaryLookup'.trans (descendantLookup'.trans
                survivorValueAtAnchor)))
        have sourceEq : primary.context.fill primary.sourceBody =
            occurrence.before := primary.source_eq
        rw [sourceEq] at primaryIff
        exact primaryIff)
    exact descendantIff.mpr descendantDenotes

private theorem Split.Description.body_sound_iff
    (description : Split.Description source)
    (model : Model)
    (environment : Values model description.occurrence.interface.external) :
    denoteRegion model environment
        (description.occurrence.targetBody description.occurrence.before) ↔
      denoteRegion model environment description.targetBody := by
  exact (description.factor_sound_iff model environment).trans
    (CompletionPlan.sound_iff description.completion model environment)

private theorem Contract.Description.body_sound_iff
    (description : Contract.Description source)
    (model : Model)
    (environment : Values model description.occurrence.interface.external) :
    denoteRegion model environment
        (description.occurrence.targetBody description.occurrence.before) ↔
      denoteRegion model environment description.targetBody := by
  exact (description.factor_sound_iff model environment).trans
    (CompletionPlan.sound_iff description.completion model environment)

theorem sound
    {source target : OpenDiagram boundary}
    (step : AnchoredWire source target)
    (model : Model) (args : Values model boundary) :
    denoteOpen model source args ↔ denoteOpen model target args := by
  cases step with
  | split canonicalSource description sourceIso targetIso =>
      rw [sourceIso.denoteOpen_iff model args,
        description.occurrence.source_iso.denoteOpen_iff model args]
      exact (OpenDiagram.denote_body_iff fun environment =>
        description.body_sound_iff model environment).trans
          (targetIso.denoteOpen_iff model args)
  | contract canonicalSource description sourceIso targetIso =>
      rw [sourceIso.denoteOpen_iff model args,
        description.occurrence.source_iso.denoteOpen_iff model args]
      exact (OpenDiagram.denote_body_iff fun environment =>
        description.body_sound_iff model environment).trans
          (targetIso.denoteOpen_iff model args)

end VisualProof.Rule.Lambda.AnchoredWire
