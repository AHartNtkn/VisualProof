# Macro-Free Higher-Order Diagram Calculus

## Objective

Execute
`docs/superpowers/plans/2026-07-30-primitive-wire-quantifier-lean-completion.md`
from the restored completed second-order architecture until:

1. the formal calculus has recursive signature-indexed wires and exactly
   atom/identity/cut diagram content, with no formalized macro system;
2. the exact 31 primitive higher-order rules have owning all-model soundness
   theorems and exhaustive `applyStep_sound` coverage;
3. replay, checked-theorem, and verified-theory soundness certify primitive
   derivations without making a theorem, definition, or reference consumable by
   a primitive step;
4. every well-typed formula in the independently defined higher-order language
   has some diagram with the same semantics; and
5. every valid direct relation substitution and comprehension has some
   primitive derivation landing at an exactly ordered-boundary-preserving raw
   target.

## Formal Boundary

The Lean formalization contains no reference nodes, definition environment,
fold/unfold, reference operations, theorem-citation step, public formula
compiler, identity canonicalizer, or direct-operation compiler. A
`TheoremSchema`, `CheckedTheorem`, or verified theory is a meta-level
certification result only and is never an input to `RuleInput` or `Step`.

The formal content constructors are exactly atom, identity, and cut. The
primitive rule sum contains exactly:

- atom spawning and identity insertion;
- identity degeneracy, one-point collapse, and same-region fusion;
- erasure, iteration, deiteration, and double-cut introduction/elimination;
- vacuous-wire introduction/elimination;
- wire join/sever, cut wrap/absorb, parallel split/fuse, and ends delete/spawn;
- arity shift/unshift, argument permutation, duplication/contraction, and
  drop/extend; and
- formal application/abstraction and identity leaf/abstraction.

## Development Contract

- Rebuild the complete macro-free production skeleton before further proof
  work. Every definition is implemented; only owning production theorem proofs
  may use `sorry` in RED.
- Lean RED/GREEN uses production declarations only. Do not create fixtures,
  redundant `example` or `#check` declarations, or test theorems.
- Port the generic second-order proof architecture and its content-parametric
  structural soundness. Do not retain second-order-specific semantic content.
- Audit every owner against both the complete SO implementation at `2bddfe4`
  and the abandoned higher-order implementation at
  `/tmp/vpa-current-lean-code-20260804-XO7NPu` before writing it. Port completed
  predecessor work with only representation-level changes. Greenfield work is
  forbidden unless the exact responsibility is absent or honestly unfinished
  in both predecessors.
- A current operation is reusable only after declaration-level comparison
  establishes substantive equivalence to its selected completed predecessor.
  Iteration uses the completed abandoned signature-indexed HO operation,
  extraction, raw-splice/insertion, factorization, semantic-equivalence, and
  terminal-soundness chain as its single basis. The SO tree at `2bddfe4` may
  supply only localized current-representation facts. Remove obsolete macro,
  definition/reference, normalization, provenance, transport, and checker
  packaging without replacing the mathematical owners consumed by
  `CheckedOrdinaryIteration.equivalence`. The current `copySelection` and
  copied-fragment simulation path is not that architecture and must not remain.
  Do not create an adapter between the two proof architectures. The three
  identity proofs and all nineteen wire-primitive proofs still port their
  completed higher-order owners.
- Formula expressiveness is existential and selects no public implementation.
- Direct substitution/comprehension completeness is existential primitive
  derivability, independent of identity normalization, canonicalization,
  macros, and compilation. The identity leaf/abstraction pair remains part of
  the nineteen relation-wire primitives needed for identity-node content.
- Exact ordered-boundary preservation belongs only to the final raw landing
  relation; it does not require receipts, transport APIs, normalization, or a
  theorem checker.
- The temporary backup at `/tmp/vpa-current-lean-code-20260804-XO7NPu` is
  implementation evidence only. Reuse a mathematical kernel only when it is
  required by the corrected plan and matches the reconstructed owner.
- The durable two-surface owner map is
  `notes/temporary-backup-salvage-map.md`; the exhaustive iteration comparison
  is `notes/iteration-declaration-audit.md`. If a selected HO iteration declaration
  cannot be adapted by the permitted localized representation edits, record its
  exact statement and the precise incompatible hypothesis or conclusion before
  proposing any new construction.

## Completion Oracle

All eight plan tasks are complete; R1-R5 have direct GREEN production owners;
the exact 31-constructor `Step` sum is exhaustively covered; no macro,
second-order-specific, normalization, compiler, receipt, transport, search,
atlas, or fixture authority remains in the formal dependency closure; and the
final axiom, build, formal-size, type, unit, and end-to-end gates pass.

## Canonical Board

`docs/goals/primitive-wire-quantifier-lean-completion/state.yaml`

## Run Command

```text
/goal Follow docs/goals/primitive-wire-quantifier-lean-completion/goal.md.
```

## PM Loop

Read this charter, the governing plan, and `state.yaml`. Work only on the active
task. Record theorem RED/GREEN evidence, direct validation, and a task commit
before activating the next task. Never infer completion from an earlier receipt;
completion requires the current production source to satisfy the oracle.
