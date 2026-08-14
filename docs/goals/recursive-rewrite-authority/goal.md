# Recursive Rule Execution

## Objective

Use recursive `OpenDiagram` syntax as the only execution representation. For
each of the five constructors of `Rule.Step`, define a computable forward
runner and a computable backward runner whose source-indexed inputs identify
one already-selected rule instance.

## Required Theorems

For each rule `R`:

```lean
(∃ index : ForwardIndex source,
    OpenDiagram.Isomorphic (runForward source index) target) ↔
  R source target

(∃ index : BackwardIndex source,
    OpenDiagram.Isomorphic (runBackward source index) target) ↔
  R target source
```

The rule must also remain true when either computed endpoint is replaced by an
isomorphic diagram.

## Execution Boundary

- Indices contain the selected source occurrence and the operands needed to
  compute the other side.
- Indices do not contain the desired target or evidence that `R` already
  holds.
- Runners do not search for occurrences or inspect a proposed target.
- Runners rebuild only the supplied recursive context.
- Proofs may use classical reasoning; runner dependency closures remain
  computable.
- Comprehension remains recursive mathematics and has no runner requirement.

## Governing Plan

`docs/superpowers/plans/2026-08-13-recursive-rule-execution.md`

## Completion Oracle

The obsolete execution closure is absent; all ten runners compile; all ten
exact iff theorems and ten endpoint-isomorphism closure theorems are
kernel-checked; the strict module checks, source audits, and full build pass.
