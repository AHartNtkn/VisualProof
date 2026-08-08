# Task 9 DoubleCut elimination public refinement report

Status: `DONE`

## Outcome

Added the structural public execution-refinement path for concrete double-cut
elimination.

- `VisualProof/Refinement/Implementation/DoubleCutElim.lean` connects the raw
  elimination trace, exact packing evidence, canonical promoted checked-open
  target, and the actual receipt target. Its `elim` theorem proves the
  canonical checked-elaboration `Rule.DoubleCut`.
- `VisualProof/Refinement/Step/DoubleCut.lean` now owns both executable members
  of the family. Its new `doubleCutElim` theorem starts from the actual
  `Concrete.execute orientation source (.doubleCutElim outer) = .ok receipt`
  equation and returns an orientation-correct `Rule.DoubleCut` together with
  `StateRepresents receipt.target`.
- The existing `doubleCutIntro` theorem is unchanged. The existing aggregate
  import of `VisualProof.Refinement.Step.DoubleCut` already exposes the complete
  family, so no aggregate source edit was required.

## Structural construction

The implementation theorem:

1. constructs `Concrete.doubleCutElimTrace rawSuccess` from the successful raw
   operation;
2. transports checked well-formedness from the realized raw result to the
   canonical promoted target;
3. splits on whether `trace.target` is the source root and invokes exactly
   `DoubleCutElimRoot.root_rule` or `DoubleCutElimContext.nested_rule`;
4. builds a concrete `OpenIso` from the canonical target to the receipt target
   through `Realizes.rawResultOpen`;
5. proves its boundary equation from `WireTransport.transportBoundary_eq_map`
   and `Realizes.transportBoundary_expected`, retaining order and repeated
   positions exactly; and
6. transports the structural relation through checked elaboration and the
   actual source and receipt arity equalities.

The family theorem inverts executor success with
`Concrete.execute_doubleCutElim_success`, invokes the implementation theorem,
uses `StateRepresents.unique` to replace the canonical source by the supplied
representation, and uses `Rule.DoubleCut.symm` only for backward orientation.

## RED/GREEN

- Implementation RED: all helper definitions and the complete `elim` signature
  compiled with `elim` as the sole proof hole in its owner.
- Implementation GREEN: `elim` compiled with a kernel-checked proof and no
  proof holes.
- Family RED: the complete public `doubleCutElim` signature compiled with its
  proof as the sole hole in the family owner.
- Family GREEN: `doubleCutIntro` and `doubleCutElim` both compiled with
  kernel-checked proofs and no holes.

## Validation

All requested bounded checks passed:

- strict compilation of
  `VisualProof/Refinement/Implementation/DoubleCutElim.lean`;
- focused build of
  `VisualProof.Refinement.Implementation.DoubleCutElim`;
- focused family build of `VisualProof.Refinement.Step.DoubleCut`;
- strict compilation of `VisualProof/Refinement/Step/DoubleCut.lean`;
- strict compilation of the aggregate `VisualProof/Refinement/Step.lean`;
- `scripts/audit-lean-authority.sh roster`;
- `scripts/audit-lean-authority.sh rules`;
- `scripts/audit-lean-authority.sh implementation`;
- `scripts/audit-lean-authority.sh proof`;
- focused scans for proof holes, semantic dependencies and soundness calls,
  examples/checks/evals, fixtures, matcher/search authority, and forbidden
  declaration prefixes; and
- `git diff --check` over the task-owned staged paths.

Only non-failing linter warnings were emitted by dependency replay. No full
build was run for this bounded family task.

## Concerns

None.
