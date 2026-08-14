import Lean.Compiler
import VisualProof.Rule.Executable

open Lean

/-! Ask Lean's code generator to compile every public runner. -/
run_meta Lean.compileDecls #[
  ``VisualProof.Rule.Erasure.runForward,
  ``VisualProof.Rule.Erasure.runBackward,
  ``VisualProof.Rule.WireSever.runForward,
  ``VisualProof.Rule.WireSever.runBackward,
  ``VisualProof.Rule.Iteration.runForward,
  ``VisualProof.Rule.Iteration.runBackward,
  ``VisualProof.Rule.DoubleCut.runForward,
  ``VisualProof.Rule.DoubleCut.runBackward,
  ``VisualProof.Rule.Vacuity.runForward,
  ``VisualProof.Rule.Vacuity.runBackward
]
