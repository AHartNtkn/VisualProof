import Lean.Compiler
import VisualProof.Concrete.Step
import VisualProof.Proof.Replay

open Lean

run_meta Lean.compileDecls #[
  ``VisualProof.Concrete.execute,
  ``VisualProof.Concrete.finish,
  ``VisualProof.Concrete.applyWireJoin,
  ``VisualProof.Concrete.applyWireSever,
  ``VisualProof.Concrete.applyErasure,
  ``VisualProof.Concrete.applyIteration,
  ``VisualProof.Concrete.applyDeiteration,
  ``VisualProof.Concrete.applyDoubleCutIntro,
  ``VisualProof.Concrete.applyDoubleCutElim,
  ``VisualProof.Concrete.applyVacuousIntro,
  ``VisualProof.Concrete.applyVacuousElim,
  ``VisualProof.Concrete.Splice.Input.spliceChecked,
  ``VisualProof.Proof.replay
]
