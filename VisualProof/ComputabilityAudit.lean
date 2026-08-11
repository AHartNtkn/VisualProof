import Lean.Compiler
import VisualProof.Concrete.Step
import VisualProof.Concrete.Operation.Structural.Validation
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
  ``VisualProof.Concrete.spliceRaw,
  ``VisualProof.Concrete.replaceSelectionRaw,
  ``VisualProof.Concrete.quotientWiresRaw,
  ``VisualProof.Concrete.splitWireRaw,
  ``VisualProof.Concrete.StructuralValidation.selectionReplacementObservation,
  ``VisualProof.Concrete.StructuralValidation.binderSpliceObservation,
  ``VisualProof.Concrete.StructuralValidation.nonterminalSpineRejected,
  ``VisualProof.Concrete.StructuralValidation.aliasedBoundaryValues,
  ``VisualProof.Concrete.StructuralValidation.splitBoundaryValues,
  ``VisualProof.Concrete.StructuralValidation.wrapperRecognitionFailures,
  ``VisualProof.Concrete.StructuralValidation.doubleCutRoundTrip,
  ``VisualProof.Concrete.StructuralValidation.doubleCutReverseRoundTrip,
  ``VisualProof.Concrete.StructuralValidation.vacuousRoundTrip,
  ``VisualProof.Concrete.StructuralValidation.vacuousReverseRoundTrip,
  ``VisualProof.Proof.replay
]
