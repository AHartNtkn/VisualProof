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
  | cutWrap
  | cutAbsorb
  | parallelSplit
  | parallelFuse
  | endsDelete
  | endsSpawn
  | arityShift
  | arityUnshift
  | argPermute
  | argDuplicate
  | argContract
  | argDrop
  | argExtend
  | applyFormal
  | abstractFormal
  | identityLeaf
  | identityAbstract
  | refLeaf
  | refAbstract
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
  , .cutWrap
  , .cutAbsorb
  , .parallelSplit
  , .parallelFuse
  , .endsDelete
  , .endsSpawn
  , .arityShift
  , .arityUnshift
  , .argPermute
  , .argDuplicate
  , .argContract
  , .argDrop
  , .argExtend
  , .applyFormal
  , .abstractFormal
  , .identityLeaf
  , .identityAbstract
  , .refLeaf
  , .refAbstract
  ]

theorem all_length : all.length = 34 := by
  decide

theorem all_nodup : all.Nodup := by
  decide

end StepTag

end VisualProof
