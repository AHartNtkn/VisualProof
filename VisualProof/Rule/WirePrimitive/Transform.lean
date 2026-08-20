import VisualProof.Diagram.Semantics.Algebra

namespace VisualProof.Rule.WirePrimitive.Transform

open Theory
open Diagram

/-- The contexts participating in one uniform rewrite. The common context
contains exactly the retained wires. -/
structure Frame (arguments common sourceWires targetWires : List Sig) where
  sourceKeep : WireRenaming common sourceWires
  targetKeep : WireRenaming common targetWires
  selected : Var sourceWires (.rel arguments)

namespace Frame

/-- Retain the wires on either side of a replaced local binder segment. -/
def localKeep (before inserted after : List Sig) :
    WireRenaming (before ++ after) (before ++ (inserted ++ after)) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (inserted ++ after))
    (fun wire => Var.appendRight before (Var.appendRight inserted wire))⟩

@[simp] theorem localKeep_cons_there
    (head : Sig) (before inserted after : List Sig)
    (wire : Var (before ++ after) signature) :
    localKeep (head :: before) inserted after (.there wire) =
      .there (localKeep before inserted after wire) := by
  apply Var.appendCases
    (motive := fun wire =>
      localKeep (head :: before) inserted after (.there wire) =
        .there (localKeep before inserted after wire))
  · intro signature retained
    calc
      localKeep (head :: before) inserted after
          (Var.there (retained.appendLeft after)) =
        (Var.there retained).appendLeft (inserted ++ after) := by
          change localKeep (head :: before) inserted after
              ((Var.there retained).appendLeft after) = _
          simp [localKeep]
      _ = Var.there (localKeep before inserted after
          (retained.appendLeft after)) := by
        simp [localKeep, Var.appendLeft]
  · intro signature trailing
    calc
      localKeep (head :: before) inserted after
          (Var.there (Var.appendRight before trailing)) =
        Var.appendRight (head :: before) (Var.appendRight inserted trailing) := by
          change localKeep (head :: before) inserted after
              (Var.appendRight (head :: before) trailing) = _
          simp [localKeep]
      _ = Var.there (localKeep before inserted after
          (Var.appendRight before trailing)) := by
        simp [localKeep, Var.appendRight]

/-- Retain the inherited context and the unaffected local binders. -/
def keep (outer before inserted after : List Sig) :
    WireRenaming (outer ++ (before ++ after))
      (outer ++ (before ++ (inserted ++ after))) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (before ++ (inserted ++ after)))
    (fun wire => Var.appendRight outer (localKeep before inserted after wire))⟩

/-- The first wire in a nonempty replacement binder segment. -/
def insertedHead (outer before after : List Sig) (signature : Sig) :
    Var (outer ++ (before ++ signature :: after)) signature :=
  Var.appendRight outer (Var.appendRight before .here)

/-- The second wire in a replacement binder segment. -/
def insertedSecond (outer before after : List Sig)
    (first second : Sig) :
    Var (outer ++ (before ++ first :: second :: after)) second :=
  Var.appendRight outer (Var.appendRight before (.there .here))

/-- The standard frame for replacing one selected relation binder. -/
def replace (outer before after targetInserted : List Sig)
    (arguments : List Sig) :
    Frame arguments (outer ++ (before ++ after))
      (outer ++ (before ++ .rel arguments :: after))
      (outer ++ (before ++ (targetInserted ++ after))) where
  sourceKeep := keep outer before [.rel arguments] after
  targetKeep := keep outer before targetInserted after
  selected := insertedHead outer before after (.rel arguments)

/-- Recursive descent preserves newly encountered local wires on both sides. -/
def append (frame : Frame arguments common sourceWires targetWires)
    (locals : List Sig) :
    Frame arguments (common ++ locals) (sourceWires ++ locals)
      (targetWires ++ locals) where
  sourceKeep := frame.sourceKeep.appendRight locals
  targetKeep := frame.targetKeep.appendRight locals
  selected := frame.selected.appendLeft locals

end Frame

namespace Values

/-- Insert a typed segment between retained prefix and suffix values. -/
def insertSegment (before : List Sig) (inserted : Values model additions) :
    Values model (before ++ after) →
      Values model (before ++ (additions ++ after)) :=
  match before with
  | [] => fun retained =>
      @Values.append model additions after inserted retained
  | _ :: rest => fun retained =>
      (retained.1, insertSegment rest inserted retained.2)

/-- Split values at an appended context boundary. -/
def splitAppend (left : List Sig) :
    Values model (left ++ right) → Values model left × Values model right :=
  match left with
  | [] => fun values => (PUnit.unit, values)
  | _ :: rest => fun values =>
      let split := splitAppend rest values.2
      ((values.1, split.1), split.2)

/-- Extract an inserted segment and the retained values around it. -/
def splitSegment (before additions after : List Sig) :
    Values model (before ++ (additions ++ after)) →
      Values model additions × Values model (before ++ after) :=
  match before with
  | [] => splitAppend additions
  | _ :: rest => fun values =>
      let split := splitSegment rest additions after values.2
      (split.1, (values.1, split.2))

theorem append_splitAppend
    (left right : List Sig) (values : Values model (left ++ right)) :
    Values.append (splitAppend left values).1 (splitAppend left values).2 =
      values := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [splitAppend, Values.append]
        rw [induction rest]

theorem insertSegment_splitSegment
    (before additions after : List Sig)
    (values : Values model (before ++ (additions ++ after))) :
    insertSegment before (splitSegment before additions after values).1
        (splitSegment before additions after values).2 = values := by
  induction before with
  | nil =>
      exact append_splitAppend additions after values
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [splitSegment, insertSegment]
        rw [induction rest]

theorem lookup_insertSegment_keep
    (before additions after : List Sig)
    (inserted : Values model additions)
    (retained : Values model (before ++ after))
    (wire : Var (before ++ after) signature) :
    (insertSegment before inserted retained).lookup
        (Frame.localKeep before additions after wire) =
      retained.lookup wire := by
  induction before with
  | nil =>
      change (Values.append inserted retained).lookup
        (Var.appendRight additions wire) = retained.lookup wire
      exact Values.lookup_append_right inserted retained wire
  | cons head rest induction =>
      cases retained with
      | mk first tail =>
        cases wire with
        | here => rfl
        | there wire =>
            rw [Frame.localKeep_cons_there]
            exact induction tail wire

theorem lookup_insertSegment_head
    (before after : List Sig) (value : denoteSig model signature)
    (rest : Values model additions)
    (retained : Values model (before ++ after)) :
    (insertSegment (additions := signature :: additions) before
      (value, rest) retained).lookup
        (Frame.insertedHead before [] (additions ++ after) signature) =
      value := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases retained with
      | mk first remaining => exact induction remaining

theorem lookup_insertSegment_second
    (before after : List Sig)
    (firstValue : denoteSig model firstSignature)
    (secondValue : denoteSig model secondSignature)
    (rest : Values model additions)
    (retained : Values model (before ++ after)) :
    (insertSegment
      (additions := firstSignature :: secondSignature :: additions) before
      (firstValue, secondValue, rest) retained).lookup
        (Frame.insertedSecond before [] (additions ++ after)
          firstSignature secondSignature) = secondValue := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases retained with
      | mk first remaining => exact induction remaining

end Values

/-- The retained common wires have the same semantic values on both sides. -/
def EnvironmentsAgree
    (frame : Frame arguments common sourceWires targetWires)
    (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires) : Prop :=
  ∀ {signature} (wire : Var common signature),
    sourceEnv.lookup (frame.sourceKeep wire) =
      targetEnv.lookup (frame.targetKeep wire)

theorem EnvironmentsAgree.replace
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (sourceRelation : denoteSig model (.rel arguments))
    (targetInserted : Values model additions) :
    EnvironmentsAgree (Frame.replace outer before after additions arguments)
      (Values.append outerEnv
        (Values.insertSegment (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit) commonLocal))
      (Values.append outerEnv
        (Values.insertSegment before targetInserted commonLocal)) := by
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (Values.append outerEnv
        (Values.insertSegment (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit)
          commonLocal)).lookup
          ((Frame.replace outer before after additions arguments).sourceKeep
            wire) =
      (Values.append outerEnv
        (Values.insertSegment before targetInserted commonLocal)).lookup
          ((Frame.replace outer before after additions arguments).targetKeep
            wire))
  · intro signature inherited
    simp [Frame.replace, Frame.keep]
  · intro signature localWire
    simp only [Frame.replace, Frame.keep, Var.appendMap_right,
      Values.lookup_append_right]
    rw [Values.lookup_insertSegment_keep,
      Values.lookup_insertSegment_keep]

theorem lookup_replace_selected
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (sourceRelation : denoteSig model (.rel arguments)) :
    (Values.append outerEnv
      (Values.insertSegment (additions := [.rel arguments]) before
        (sourceRelation, PUnit.unit)
        commonLocal)).lookup
        (Frame.replace outer before after additions arguments).selected =
      sourceRelation := by
  rw [show (Frame.replace outer before after additions arguments).selected =
    Var.appendRight outer
      (Frame.insertedHead before [] after (.rel arguments)) by rfl]
  induction outer with
  | nil =>
      exact Values.lookup_insertSegment_head (additions := []) before after
        sourceRelation (PUnit.unit : Values model []) commonLocal
  | cons head tail induction =>
      cases outerEnv with
      | mk first rest => exact induction rest

theorem lookup_replace_targetHead
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (targetValue : denoteSig model signature)
    (targetRest : Values model additions) :
      (Values.append outerEnv
        (Values.insertSegment (additions := signature :: additions) before
          (targetValue, targetRest)
        commonLocal)).lookup
        (Frame.insertedHead outer before (additions ++ after) signature) =
      targetValue := by
  rw [show Frame.insertedHead outer before (additions ++ after) signature =
    Var.appendRight outer
      (Frame.insertedHead before [] (additions ++ after) signature) by rfl]
  induction outer with
  | nil =>
      exact Values.lookup_insertSegment_head before after targetValue
        targetRest commonLocal
  | cons head tail induction =>
      cases outerEnv with
      | mk first rest => exact induction rest

theorem lookup_replace_targetSecond
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (firstValue : denoteSig model firstSignature)
    (secondValue : denoteSig model secondSignature)
    (targetRest : Values model additions) :
    (Values.append outerEnv
      (Values.insertSegment
        (additions := firstSignature :: secondSignature :: additions) before
        (firstValue, secondValue, targetRest) commonLocal)).lookup
        (Frame.insertedSecond outer before (additions ++ after)
          firstSignature secondSignature) = secondValue := by
  rw [show Frame.insertedSecond outer before (additions ++ after)
      firstSignature secondSignature =
    Var.appendRight outer (Frame.insertedSecond before []
      (additions ++ after) firstSignature secondSignature) by rfl]
  induction outer with
  | nil =>
      exact Values.lookup_insertSegment_second before after firstValue
        secondValue targetRest commonLocal
  | cons head tail induction =>
      cases outerEnv with
      | mk first rest => exact induction rest

/-- A uniform operation supplies its target-side distinguished wires, their
lifting beneath local binders, the site syntax, and the one shared semantic
witness invariant used at every site. -/
structure Operation (arguments : List Sig) where
  Data : ∀ {common sourceWires targetWires},
    Frame arguments common sourceWires targetWires → Type
  appendData :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      Data frame → ∀ locals, Data (frame.append locals)
  site :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      Data frame → Vars common arguments → Region targetWires → Prop

namespace Operation

/-- Semantic evidence for a syntactic uniform operation. Kept separate so a
rule relation contains no model-indexed premise. -/
structure Sound (operation : Operation arguments) where
  Realizes :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      operation.Data frame → (model : Model) → Values model sourceWires →
        Values model targetWires → Prop
  realizes_append :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : operation.Data frame) (model : Model)
      (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires),
      Realizes frame data model sourceEnv targetEnv →
      ∀ {locals} (localEnv : Values model locals),
        Realizes (frame.append locals)
          (operation.appendData frame data locals) model
          (Values.append sourceEnv localEnv)
          (Values.append targetEnv localEnv)
  site_sound :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : operation.Data frame) (ports : Vars common arguments)
      (target : Region targetWires),
      operation.site frame data ports target →
      ∀ (model : Model) (sourceEnv : Values model sourceWires)
        (targetEnv : Values model targetWires),
        EnvironmentsAgree frame sourceEnv targetEnv →
        Realizes frame data model sourceEnv targetEnv →
        (sourceEnv.lookup frame.selected
            (evaluateVars
              (ports.map fun wire => frame.sourceKeep wire) sourceEnv) ↔
          denoteRegion model targetEnv target)

end Operation

mutual
  /-- A recursive uniform transformation beneath locally bound wires. -/
  inductive RegionResult (operation : Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      (frame : Frame arguments common sourceWires targetWires) →
      operation.Data frame →
      Region sourceWires → Region targetWires → Prop
    | mk
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        {result : Region (targetWires ++ locals)}
        (itemsResult : ItemsResult operation (frame.append locals)
          (operation.appendData frame data locals) items result) :
        RegionResult operation frame data (.mk locals items)
          (Region.adjoinAt locals .nil result)

  /-- A source conjunction becomes the conjunction of its transformed item
  regions. Site replacements may bind fresh wires locally. -/
  inductive ItemsResult (operation : Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      (frame : Frame arguments common sourceWires targetWires) →
      operation.Data frame →
      ItemSeq sourceWires → Region targetWires → Prop
    | nil
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame} :
        ItemsResult operation frame data .nil (Region.blank targetWires)
    | cons
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        {itemResult tailResult : Region targetWires}
        (itemEvidence : ItemResult operation frame data item itemResult)
        (tailEvidence : ItemsResult operation frame data tail tailResult) :
        ItemsResult operation frame data (.cons item tail)
          (itemResult.conjoin tailResult)

  /-- Every non-selected item is reconstructed from retained wires. The
  selected wire is accepted only as an atom head, which enforces that all of
  its incidences are applications. -/
  inductive ItemResult (operation : Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      (frame : Frame arguments common sourceWires targetWires) →
      operation.Data frame →
      Item sourceWires → Region targetWires → Prop
    | atom
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (head : Var common (.rel atomArguments))
        (ports : Vars common atomArguments) :
        ItemResult operation frame data
          (.atom (frame.sourceKeep head)
            (ports.map fun wire => frame.sourceKeep wire))
          (Region.singleton (.atom (frame.targetKeep head)
            (ports.map fun wire => frame.targetKeep wire)))
    | selectedAtom
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (ports : Vars common arguments)
        {target : Region targetWires}
        (evidence : operation.site frame data ports target) :
        ItemResult operation frame data
          (.atom frame.selected
            (ports.map fun wire => frame.sourceKeep wire)) target
    | identity
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var common signature) :
        ItemResult operation frame data
          (.identity signature arity
            (fun index => frame.sourceKeep (ports index)))
          (Region.singleton (.identity signature arity
            (fun index => frame.targetKeep (ports index))))
    | cut
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {body : Region sourceWires} {result : Region targetWires}
        (bodyEvidence : RegionResult operation frame data body result) :
        ItemResult operation frame data (.cut body)
          (Region.singleton (.cut result))
end

private theorem EnvironmentsAgree.append
    {arguments common sourceWires targetWires locals : List Sig}
    {frame : Frame arguments common sourceWires targetWires}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (agree : EnvironmentsAgree frame sourceEnv targetEnv)
    (localEnv : Values model locals) :
    EnvironmentsAgree (frame.append locals)
      (Values.append sourceEnv localEnv)
      (Values.append targetEnv localEnv) := by
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (sourceEnv.append localEnv).lookup
          ((frame.append locals).sourceKeep wire) =
        (targetEnv.append localEnv).lookup
          ((frame.append locals).targetKeep wire))
  · intro signature inherited
    simpa [Frame.append, WireRenaming.appendRight] using agree inherited
  · intro signature localWire
    simp [Frame.append, WireRenaming.appendRight]

theorem evaluate_retained_eq
    {arguments common sourceWires targetWires signatures : List Sig}
    {frame : Frame arguments common sourceWires targetWires}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (ports : Vars common signatures)
    (agree : EnvironmentsAgree frame sourceEnv targetEnv) :
    evaluateVars (ports.map fun wire => frame.sourceKeep wire) sourceEnv =
      evaluateVars (ports.map fun wire => frame.targetKeep wire) targetEnv := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, evaluateVars]
      rw [agree head, induction]

theorem denote_singleton_iff
    (item : Item wires) (model : Model) (env : Values model wires) :
    denoteRegion model env (Region.singleton item) ↔
      denoteItem model env item := by
  unfold Region.singleton Region.ofItems
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  change (∃ localEnv : Values model [],
      denoteItemSeq model (env.append localEnv)
        ((ItemSeq.cons item .nil).renameWires appendNil)) ↔ _
  have envEq (localEnv : Values model []) :
      Values.rename appendNil (env.append localEnv) = env := by
    apply Values.ext
    intro signature wire
    simp [appendNil]
  constructor
  · rintro ⟨localEnv, itemDenotes, _⟩
    have renamed := (denoteItem_renameWires model appendNil
      (env.append localEnv) item).mp itemDenotes
    rwa [envEq] at renamed
  · intro itemDenotes
    refine ⟨PUnit.unit, ?_, trivial⟩
    apply (denoteItem_renameWires model appendNil
      (env.append PUnit.unit) item).mpr
    rwa [envEq]

theorem denote_blank_iff (model : Model) (env : Values model wires) :
    denoteRegion model env (Region.blank wires) ↔ True := by
  unfold Region.blank
  constructor
  · intro
    trivial
  · intro
    exact ⟨PUnit.unit, trivial⟩

mutual
  theorem RegionResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      (operationSound : operation.Sound)
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {target : Region targetWires}
      (step : RegionResult operation frame data source target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operationSound.Realizes frame data model sourceEnv targetEnv) :
      denoteRegion model sourceEnv source ↔
        denoteRegion model targetEnv target := by
    cases step with
    | @mk _ _ _ _ _ locals items result itemsResult =>
      simp only [denoteRegion_mk]
      rw [Region.denote_adjoinAt]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, trivial,
          (itemsResult.sound_iff operationSound model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)
            (operationSound.realizes_append frame data model sourceEnv targetEnv
              realizes localEnv)).mp itemsDenote⟩
      · rintro ⟨localEnv, _, resultDenotes⟩
        exact ⟨localEnv,
          (itemsResult.sound_iff operationSound model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)
            (operationSound.realizes_append frame data model sourceEnv targetEnv
              realizes localEnv)).mpr resultDenotes⟩

  theorem ItemsResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      (operationSound : operation.Sound)
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {items : ItemSeq sourceWires} {target : Region targetWires}
      (step : ItemsResult operation frame data items target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operationSound.Realizes frame data model sourceEnv targetEnv) :
      denoteItemSeq model sourceEnv items ↔
        denoteRegion model targetEnv target := by
    cases step with
    | nil =>
      change True ↔ ∃ localEnv : Values model [], True
      constructor
      · intro
        exact ⟨PUnit.unit, trivial⟩
      · intro
        trivial
    | cons itemEvidence tailEvidence =>
      rw [denoteItemSeq_cons, Region.denote_conjoin]
      exact and_congr
        (itemEvidence.sound_iff operationSound model sourceEnv targetEnv
          agree realizes)
        (tailEvidence.sound_iff operationSound model sourceEnv targetEnv
          agree realizes)

  theorem ItemResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      (operationSound : operation.Sound)
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {item : Item sourceWires} {target : Region targetWires}
      (step : ItemResult operation frame data item target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operationSound.Realizes frame data model sourceEnv targetEnv) :
      denoteItem model sourceEnv item ↔
        denoteRegion model targetEnv target := by
    cases step with
    | atom head ports =>
      rw [denote_singleton_iff]
      simp only [denoteItem_atom]
      rw [agree head, evaluate_retained_eq ports agree]
    | selectedAtom ports evidence =>
      exact operationSound.site_sound frame data ports _ evidence model sourceEnv
        targetEnv agree realizes
    | identity signature arity ports =>
      rw [denote_singleton_iff]
      simp only [denoteItem_identity]
      constructor
      · intro sourceDenotes left right
        rw [← agree (ports left), ← agree (ports right)]
        exact sourceDenotes left right
      · intro targetDenotes left right
        rw [agree (ports left), agree (ports right)]
        exact targetDenotes left right
    | cut bodyEvidence =>
      rw [denote_singleton_iff]
      simp only [denoteItem_cut]
      exact not_congr
        (bodyEvidence.sound_iff operationSound model sourceEnv targetEnv agree
          realizes)
end

end VisualProof.Rule.WirePrimitive.Transform
