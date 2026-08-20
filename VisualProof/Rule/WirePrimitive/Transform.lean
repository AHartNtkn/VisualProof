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

/-- Recursive descent preserves newly encountered local wires on both sides. -/
def append (frame : Frame arguments common sourceWires targetWires)
    (locals : List Sig) :
    Frame arguments (common ++ locals) (sourceWires ++ locals)
      (targetWires ++ locals) where
  sourceKeep := frame.sourceKeep.appendRight locals
  targetKeep := frame.targetKeep.appendRight locals
  selected := frame.selected.appendLeft locals

end Frame

/-- The retained common wires have the same semantic values on both sides. -/
def EnvironmentsAgree
    (frame : Frame arguments common sourceWires targetWires)
    (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires) : Prop :=
  ∀ {signature} (wire : Var common signature),
    sourceEnv.lookup (frame.sourceKeep wire) =
      targetEnv.lookup (frame.targetKeep wire)

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
  Realizes :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      Data frame → (model : Model) → Values model sourceWires →
        Values model targetWires → Prop
  realizes_append :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : Data frame) (model : Model)
      (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires),
      Realizes frame data model sourceEnv targetEnv →
      ∀ {locals} (localEnv : Values model locals),
        Realizes (frame.append locals) (appendData frame data locals) model
          (Values.append sourceEnv localEnv)
          (Values.append targetEnv localEnv)
  site_sound :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : Data frame) (ports : Vars common arguments)
      (target : Region targetWires),
      site frame data ports target →
      ∀ (model : Model) (sourceEnv : Values model sourceWires)
        (targetEnv : Values model targetWires),
        EnvironmentsAgree frame sourceEnv targetEnv →
        Realizes frame data model sourceEnv targetEnv →
        (sourceEnv.lookup frame.selected
            (evaluateVars
              (ports.map fun wire => frame.sourceKeep wire) sourceEnv) ↔
          denoteRegion model targetEnv target)

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

private theorem evaluate_retained_eq
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

private theorem denote_singleton_iff
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

mutual
  theorem RegionResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {target : Region targetWires}
      (step : RegionResult operation frame data source target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operation.Realizes frame data model sourceEnv targetEnv) :
      denoteRegion model sourceEnv source ↔
        denoteRegion model targetEnv target := by
    cases step with
    | @mk _ _ _ _ _ locals items result itemsResult =>
      simp only [denoteRegion_mk]
      rw [Region.denote_adjoinAt]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, trivial,
          (itemsResult.sound_iff model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)
            (operation.realizes_append frame data model sourceEnv targetEnv
              realizes localEnv)).mp itemsDenote⟩
      · rintro ⟨localEnv, _, resultDenotes⟩
        exact ⟨localEnv,
          (itemsResult.sound_iff model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)
            (operation.realizes_append frame data model sourceEnv targetEnv
              realizes localEnv)).mpr resultDenotes⟩

  theorem ItemsResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {items : ItemSeq sourceWires} {target : Region targetWires}
      (step : ItemsResult operation frame data items target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operation.Realizes frame data model sourceEnv targetEnv) :
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
        (itemEvidence.sound_iff model sourceEnv targetEnv agree realizes)
        (tailEvidence.sound_iff model sourceEnv targetEnv agree realizes)

  theorem ItemResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {item : Item sourceWires} {target : Region targetWires}
      (step : ItemResult operation frame data item target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operation.Realizes frame data model sourceEnv targetEnv) :
      denoteItem model sourceEnv item ↔
        denoteRegion model targetEnv target := by
    cases step with
    | atom head ports =>
      rw [denote_singleton_iff]
      simp only [denoteItem_atom]
      rw [agree head, evaluate_retained_eq ports agree]
    | selectedAtom ports evidence =>
      exact operation.site_sound frame data ports _ evidence model sourceEnv
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
        (bodyEvidence.sound_iff model sourceEnv targetEnv agree realizes)
end

end VisualProof.Rule.WirePrimitive.Transform
