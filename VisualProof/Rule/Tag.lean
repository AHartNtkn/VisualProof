namespace VisualProof

/-- The complete primitive proof-step vocabulary, in durable replay order. -/
inductive StepTag
  | refSpawn
  | atomSpawn
  | identityInsert
  | wireJoin
  | erasure
  | wireSever
  | iteration
  | deiteration
  | doubleCutIntro
  | doubleCutElim
  | theorem
  | vacuousIntro
  | vacuousElim
  | unfold
  | fold
  deriving Repr, DecidableEq

namespace StepTag

/-- Every primitive tag, in the exact durable proof-language order. -/
def all : List StepTag :=
  [ .refSpawn
  , .atomSpawn
  , .identityInsert
  , .wireJoin
  , .erasure
  , .wireSever
  , .iteration
  , .deiteration
  , .doubleCutIntro
  , .doubleCutElim
  , .theorem
  , .vacuousIntro
  , .vacuousElim
  , .unfold
  , .fold
  ]

theorem all_length : all.length = 15 := by
  decide

theorem all_nodup : all.Nodup := by
  decide

end StepTag

end VisualProof
