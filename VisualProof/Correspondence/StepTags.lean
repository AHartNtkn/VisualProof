import VisualProof.Rule.Step

namespace VisualProof.Rule.StepTag

/-- The sole wire-format spelling for each logical rule constructor.  Runtime
correspondence checks compare this projection of `StepTag.all` directly with
the TypeScript `ProofStep` discriminants. -/
def serializedName : StepTag → String
  | .openTermSpawn => "openTermSpawn"
  | .relationSpawn => "relationSpawn"
  | .boundRelationSpawn => "boundRelationSpawn"
  | .wireJoin => "wireJoin"
  | .erasure => "erasure"
  | .wireSever => "wireSever"
  | .iteration => "iteration"
  | .deiteration => "deiteration"
  | .doubleCutIntro => "doubleCutIntro"
  | .doubleCutElim => "doubleCutElim"
  | .inconsistentCutElim => "inconsistentCutElim"
  | .conversion => "conversion"
  | .congruenceJoin => "congruenceJoin"
  | .anchoredWireSplit => "anchoredWireSplit"
  | .anchoredWireContract => "anchoredWireContract"
  | .headStrip => "headStrip"
  | .closedTermIntro => "closedTermIntro"
  | .fusion => "fusion"
  | .fission => "fission"
  | .comprehensionInstantiate => "comprehensionInstantiate"
  | .comprehensionAbstract => "comprehensionAbstract"
  | .theorem => "theorem"
  | .vacuousIntro => "vacuousIntro"
  | .vacuousElim => "vacuousElim"
  | .relUnfold => "relUnfold"
  | .relFold => "relFold"

def serializedAll : List String := StepTag.all.map serializedName

theorem serializedName_injective : Function.Injective serializedName := by
  intro left right equality
  cases left <;> cases right <;> simp_all [serializedName]

theorem serializedAll_length : serializedAll.length = 26 := by
  simpa [serializedAll] using StepTag.all_length

theorem serializedAll_nodup : serializedAll.Nodup := by
  exact List.Pairwise.map serializedName
    (fun _ _ distinct equality => distinct (serializedName_injective equality))
    StepTag.all_nodup

end VisualProof.Rule.StepTag
