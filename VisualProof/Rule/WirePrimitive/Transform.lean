import VisualProof.Diagram.Semantics.Algebra

namespace VisualProof.Rule.WirePrimitive.Transform

open Theory
open Diagram

/-- An operation-specific replacement for one application of the selected
relation wire. The common context contains every retained wire; the two
renamings embed it into the source and target contexts. -/
structure SiteRule (arguments : List Sig) where
  holds :
    ∀ {common sourceWires targetWires : List Sig},
      WireRenaming common sourceWires →
      WireRenaming common targetWires →
      Var sourceWires (.rel arguments) →
      Vars common arguments →
      Region targetWires → Prop

mutual
  /-- A recursive uniform transformation beneath locally bound wires. -/
  inductive RegionResult (arguments : List Sig) (site : SiteRule arguments) :
      {common sourceWires targetWires : List Sig} →
      WireRenaming common sourceWires →
      WireRenaming common targetWires →
      Var sourceWires (.rel arguments) →
      Region sourceWires → Region targetWires → Prop
    | mk
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        {result : Region (targetWires ++ locals)}
        (itemsResult : ItemsResult arguments site
          (sourceKeep.appendRight locals)
          (targetKeep.appendRight locals)
          (selected.appendLeft locals) items result) :
        RegionResult arguments site sourceKeep targetKeep selected
          (.mk locals items) (Region.adjoinAt locals .nil result)

  /-- A source conjunction becomes the conjunction of its transformed item
  regions. Site replacements may bind fresh wires locally. -/
  inductive ItemsResult (arguments : List Sig) (site : SiteRule arguments) :
      {common sourceWires targetWires : List Sig} →
      WireRenaming common sourceWires →
      WireRenaming common targetWires →
      Var sourceWires (.rel arguments) →
      ItemSeq sourceWires → Region targetWires → Prop
    | nil
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)} :
        ItemsResult arguments site sourceKeep targetKeep selected .nil
          (Region.blank targetWires)
    | cons
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        {itemResult tailResult : Region targetWires}
        (itemEvidence : ItemResult arguments site sourceKeep targetKeep selected
          item itemResult)
        (tailEvidence : ItemsResult arguments site sourceKeep targetKeep selected
          tail tailResult) :
        ItemsResult arguments site sourceKeep targetKeep selected (.cons item tail)
          (itemResult.conjoin tailResult)

  /-- Every non-selected item is reconstructed from retained wires. The
  selected wire is accepted only as an atom head, which enforces that all of
  its incidences are applications. -/
  inductive ItemResult (arguments : List Sig) (site : SiteRule arguments) :
      {common sourceWires targetWires : List Sig} →
      WireRenaming common sourceWires →
      WireRenaming common targetWires →
      Var sourceWires (.rel arguments) →
      Item sourceWires → Region targetWires → Prop
    | atom
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)}
        (head : Var common (.rel atomArguments))
        (ports : Vars common atomArguments) :
        ItemResult arguments site sourceKeep targetKeep selected
          (.atom (sourceKeep head)
            (ports.map fun wire => sourceKeep wire))
          (Region.singleton (.atom (targetKeep head)
            (ports.map fun wire => targetKeep wire)))
    | selectedAtom
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)}
        (ports : Vars common arguments)
        {target : Region targetWires}
        (evidence : site.holds sourceKeep targetKeep selected ports target) :
        ItemResult arguments site sourceKeep targetKeep selected
          (.atom selected (ports.map fun wire => sourceKeep wire)) target
    | identity
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var common signature) :
        ItemResult arguments site sourceKeep targetKeep selected
          (.identity signature arity (fun index => sourceKeep (ports index)))
          (Region.singleton (.identity signature arity
            (fun index => targetKeep (ports index))))
    | cut
        {sourceKeep : WireRenaming common sourceWires}
        {targetKeep : WireRenaming common targetWires}
        {selected : Var sourceWires (.rel arguments)}
        {body : Region sourceWires} {result : Region targetWires}
        (bodyEvidence : RegionResult arguments site sourceKeep targetKeep selected
          body result) :
        ItemResult arguments site sourceKeep targetKeep selected (.cut body)
          (Region.singleton (.cut result))
end

/-- The retained common wires have the same semantic values on both sides. -/
def EnvironmentsAgree
    (sourceKeep : WireRenaming common sourceWires)
    (targetKeep : WireRenaming common targetWires)
    (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires) : Prop :=
  ∀ {signature} (wire : Var common signature),
    sourceEnv.lookup (sourceKeep wire) = targetEnv.lookup (targetKeep wire)

/-- The operation-specific site relation has the intended pointwise
semantics whenever retained wire environments agree. -/
def SiteSound (site : SiteRule arguments) : Prop :=
  ∀ {common sourceWires targetWires}
    (sourceKeep : WireRenaming common sourceWires)
    (targetKeep : WireRenaming common targetWires)
    (selected : Var sourceWires (.rel arguments))
    (ports : Vars common arguments) (target : Region targetWires),
    site.holds sourceKeep targetKeep selected ports target →
    ∀ (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires),
      EnvironmentsAgree sourceKeep targetKeep sourceEnv targetEnv →
      (sourceEnv.lookup selected
          (evaluateVars (ports.map fun wire => sourceKeep wire) sourceEnv) ↔
        denoteRegion model targetEnv target)

private theorem EnvironmentsAgree.append
    {common sourceWires targetWires locals : List Sig}
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (agree : EnvironmentsAgree sourceKeep targetKeep sourceEnv targetEnv)
    (localEnv : Values model locals) :
    EnvironmentsAgree (sourceKeep.appendRight locals)
      (targetKeep.appendRight locals)
      (Values.append (model := model) sourceEnv localEnv)
      (Values.append (model := model) targetEnv localEnv) := by
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (sourceEnv.append localEnv).lookup
          (sourceKeep.appendRight locals wire) =
        (targetEnv.append localEnv).lookup
          (targetKeep.appendRight locals wire))
  · intro signature inherited
    simpa [WireRenaming.appendRight] using agree inherited
  · intro signature localWire
    simp [WireRenaming.appendRight]

private theorem evaluate_retained_eq
    {common sourceWires targetWires signatures : List Sig}
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (ports : Vars common signatures)
    (agree : EnvironmentsAgree sourceKeep targetKeep sourceEnv targetEnv) :
    evaluateVars (ports.map fun wire => sourceKeep wire) sourceEnv =
      evaluateVars (ports.map fun wire => targetKeep wire) targetEnv := by
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
      {site : SiteRule arguments}
      {sourceKeep : WireRenaming common sourceWires}
      {targetKeep : WireRenaming common targetWires}
      {selected : Var sourceWires (.rel arguments)}
      {source : Region sourceWires} {target : Region targetWires}
      (siteSound : SiteSound site)
      (step : RegionResult arguments site sourceKeep targetKeep selected source target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree sourceKeep targetKeep sourceEnv targetEnv) :
      denoteRegion model sourceEnv source ↔
        denoteRegion model targetEnv target := by
    cases step with
    | @mk _ _ _ _ _ _ locals items result itemsResult =>
      simp only [denoteRegion_mk]
      rw [Region.denote_adjoinAt]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, trivial,
          (itemsResult.sound_iff siteSound model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)).mp itemsDenote⟩
      · rintro ⟨localEnv, _, resultDenotes⟩
        exact ⟨localEnv,
          (itemsResult.sound_iff siteSound model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)).mpr resultDenotes⟩

  theorem ItemsResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {site : SiteRule arguments}
      {sourceKeep : WireRenaming common sourceWires}
      {targetKeep : WireRenaming common targetWires}
      {selected : Var sourceWires (.rel arguments)}
      {items : ItemSeq sourceWires} {target : Region targetWires}
      (siteSound : SiteSound site)
      (step : ItemsResult arguments site sourceKeep targetKeep selected items target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree sourceKeep targetKeep sourceEnv targetEnv) :
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
        (itemEvidence.sound_iff siteSound model sourceEnv targetEnv agree)
        (tailEvidence.sound_iff siteSound model sourceEnv targetEnv agree)

  theorem ItemResult.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {site : SiteRule arguments}
      {sourceKeep : WireRenaming common sourceWires}
      {targetKeep : WireRenaming common targetWires}
      {selected : Var sourceWires (.rel arguments)}
      {item : Item sourceWires} {target : Region targetWires}
      (siteSound : SiteSound site)
      (step : ItemResult arguments site sourceKeep targetKeep selected item target)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree sourceKeep targetKeep sourceEnv targetEnv) :
      denoteItem model sourceEnv item ↔
        denoteRegion model targetEnv target := by
    cases step with
    | atom head ports =>
      rw [denote_singleton_iff]
      simp only [denoteItem_atom]
      rw [agree head, evaluate_retained_eq ports agree]
    | selectedAtom ports evidence =>
      exact siteSound _ _ _ ports _ evidence model sourceEnv targetEnv agree
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
        (bodyEvidence.sound_iff siteSound model sourceEnv targetEnv agree)
end

end VisualProof.Rule.WirePrimitive.Transform
