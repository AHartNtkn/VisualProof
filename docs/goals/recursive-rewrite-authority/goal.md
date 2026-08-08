# Recursive Rewrite Authority

## Objective

Reconstruct the diagram-rewriting architecture so recursive diagrams, relational rewrite rules, and recursive semantics are the proof-theoretic authority, while flat diagrams and executable rewriting are certified implementations connected only by representation and refinement proofs.

## Original Request

Refactor the complete calculus to ordinary relational recursive-diagram rewriting modulo isomorphism, certify the concrete implementation against it, use subagent-driven development to plan and execute the work to completion, and create and follow a `/goal`.

## Intake Summary

- Input shape: `existing_plan`
- Audience: maintainers and users relying on kernel-checked rule soundness
- Authority: `requested`
- Proof type: `test`
- Completion proof: the Lean development builds without incomplete definitions, the five executable recursive rule families factor through `Step.sound`, standalone Comprehension remains recursive mathematics outside the actual ruleset, and every successful concrete transition has a Lean refinement proof into `Step`
- Goal oracle: kernel-checked Lean theorems demonstrate the requested authority boundary and the final audit records `full_outcome_complete: true`
- Likely misfire: adding abstract wrappers while leaving concrete execution data as the real rule or semantic authority
- Blind spots considered: bound-wire equivalence, repeated boundary aliases, iteration selections that overlap the ordered boundary, inherently simultaneous rules, capture avoidance, ordered interfaces, representation uniqueness, and the distinction between executor soundness and executor completeness
- Existing plan facts: recursive diagrams own mathematical syntax and structural semantics; occurrence is context-decomposition evidence; local rules use contextual closure modulo isomorphism; whole-diagram rules use direct relations; `Step.sound` contains no execution artifacts; concrete diagrams represent recursive diagrams; execution correctness is refinement; all rule families and dependents migrate without compatibility authorities

## Goal Oracle

The oracle for this goal is:

`lake build` passes and kernel-checked theorem declarations establish one recursive relational calculus, structural recursive semantics, and a separate concrete representation/refinement layer.

The PM must keep comparing task receipts to this oracle. Planning, discovery, a passing tiny slice, or a clean-looking board is not enough. The goal finishes only when a final Judge/PM audit maps receipts and verification back to this oracle and records `full_outcome_complete: true`.

## Goal Kind

`existing_plan`

## Current Tranche

Execute the reviewed implementation plan in successive theorem-driven Worker packages until the recursive authority and concrete refinement boundary is complete.

## Non-Negotiable Constraints

- Recursive open diagrams and their structural denotation are the sole mathematical syntax and semantic authority.
- The five executable recursive rule families are propositions over recursive diagrams; `Step` is their exhaustive inductive union, while standalone Comprehension remains recursive mathematics outside the actual ruleset.
- Occurrence is context decomposition evidence, never a search algorithm or execution result.
- Local rules use contextual closure modulo recursive isomorphism; global and simultaneous rules retain direct relational statements.
- Rule soundness mentions no concrete carriers, numbering, execution state, trace, receipt, request, or error.
- Concrete correctness is representation and refinement, including ordered interfaces and repeated aliases; it does not directly define semantic preservation.
- The Iteration request carries exact boundary-disjointness evidence; reflection, execution refinement, and exact-request meaning use that evidence without changing the recursive rule or adding an executor rejection class.
- The Lean formalization has no matcher or occurrence-search subsystem; requests supply occurrence evidence.
- Representation completeness and one-step execution completeness are required.
- TypeScript is outside this goal's implementation, planning, and validation scope.
- No aliases, adapters, compatibility modes, parallel authorities, or fallback semantics preserve the displaced model.
- Lean proof work follows theorem-driven RED/GREEN; no incomplete production definitions are permitted.
- Preserve unrelated user work, validate behavior-affecting changes, and commit every completed task-owned package.

## Stop Rule

Stop only when a final audit proves the full original outcome is complete and the machine-checkable GoalBuddy stop gate passes.

## Canonical Board

Machine truth lives at:

`docs/goals/recursive-rewrite-authority/state.yaml`

## Run Command

`/goal Follow docs/goals/recursive-rewrite-authority/goal.md.`
