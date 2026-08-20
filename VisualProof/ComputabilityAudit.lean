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
  ``VisualProof.Rule.Vacuity.runBackward,
  ``VisualProof.Rule.Presentation.runForward,
  ``VisualProof.Rule.Presentation.runBackward,
  ``VisualProof.Rule.Identification.runForward,
  ``VisualProof.Rule.Identification.runBackward,
  ``VisualProof.Rule.WirePrimitive.CutShape.runForward,
  ``VisualProof.Rule.WirePrimitive.CutShape.runBackward,
  ``VisualProof.Rule.WirePrimitive.ParallelShape.runForward,
  ``VisualProof.Rule.WirePrimitive.ParallelShape.runBackward,
  ``VisualProof.Rule.WirePrimitive.Ends.runForward,
  ``VisualProof.Rule.WirePrimitive.Ends.runBackward,
  ``VisualProof.Rule.WirePrimitive.Arity.runForward,
  ``VisualProof.Rule.WirePrimitive.Arity.runBackward,
  ``VisualProof.Rule.WirePrimitive.ArgumentPermutation.runForward,
  ``VisualProof.Rule.WirePrimitive.ArgumentPermutation.runBackward,
  ``VisualProof.Rule.WirePrimitive.ArgumentDuplicate.runForward,
  ``VisualProof.Rule.WirePrimitive.ArgumentDuplicate.runBackward,
  ``VisualProof.Rule.WirePrimitive.ArgumentProjection.runForward,
  ``VisualProof.Rule.WirePrimitive.ArgumentProjection.runBackward,
  ``VisualProof.Rule.WirePrimitive.FormalApplication.runForward,
  ``VisualProof.Rule.WirePrimitive.FormalApplication.runBackward,
  ``VisualProof.Rule.WirePrimitive.IdentityLeaf.runForward,
  ``VisualProof.Rule.WirePrimitive.IdentityLeaf.runBackward
]
