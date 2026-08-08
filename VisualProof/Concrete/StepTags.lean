import VisualProof.Concrete.Step

namespace VisualProof.Concrete.StepTag

open VisualProof.Concrete

/-- The sole wire-format spelling for each logical rule constructor.  Runtime
correspondence checks compare this projection of `StepTag.all` directly with
the TypeScript `ProofStep` discriminants. -/
def serializedName : StepTag → String
  | .boundRelationSpawn => "boundRelationSpawn"
  | .wireJoin => "wireJoin"
  | .erasure => "erasure"
  | .wireSever => "wireSever"
  | .iteration => "iteration"
  | .deiteration => "deiteration"
  | .doubleCutIntro => "doubleCutIntro"
  | .doubleCutElim => "doubleCutElim"
  | .vacuousIntro => "vacuousIntro"
  | .vacuousElim => "vacuousElim"

def serializedAll : List String := StepTag.all.map serializedName

theorem serializedName_injective : Function.Injective serializedName := by
  intro left right equality
  cases left <;> cases right <;> simp_all [serializedName]

theorem serializedAll_length : serializedAll.length = 10 := by
  simpa [serializedAll] using StepTag.all_length

theorem serializedAll_nodup : serializedAll.Nodup := by
  exact List.Pairwise.map serializedName
    (fun _ _ distinct equality => distinct (serializedName_injective equality))
    StepTag.all_nodup

end VisualProof.Concrete.StepTag
