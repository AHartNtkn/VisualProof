# Game Structural Delete Selection Design

**Status:** Approved
**Date:** 2026-07-22

## Outcome

In game interactions, Delete and Backspace use the complete highlighted selection
when deciding whether the player intends double-cut or trivial-quantifier
elimination. Extra highlighted interior content suppresses those structural rules
and allows the existing later deletion rules to run. The established macro for
eliminating several selected trivial quantifiers remains atomic and unchanged for
valid selections.

## Game-Only Scope

This design changes `GameProofMoveController` and its game-owned discovery helpers.
It does not change the shared non-game proof controller, global selection
normalization, or kernel rule appliers.

Game deletion preserves two views of the interaction:

- Exact hits record every semantic figure highlighted by the player and determine
  structural-elimination intent.
- The absorb-normalized `SubgraphSelection` remains the input for erasure,
  deiteration, and the other existing proof rules.

## Structural Intent

Double-cut elimination is eligible only for either exact selection:

1. the outer cut;
2. the outer cut and its directly nested inner cut.

Single trivial-quantifier elimination is eligible only when one vacuous bubble is
the complete selection. A node, wire, cut, nested boundary, or any other extra hit
suppresses the single action.

The multi-quantifier macro retains its current contract. Two or more distinct
selected region hits must all be bubbles and must form one gapless nested
parent-child chain. The controller preflights the ordinary vacuous eliminations and
commits them deepest-first as one `ProofAction`, clearing selection once.

A selection containing multiple bubble rims plus any non-bubble hit is not a macro
request. It falls through to ordinary deletion. A selection made exclusively of
multiple bubble rims but failing the macro's gapless-chain or vacuity requirements
retains the existing focused refusal.

## Discovery and Dispatch

Game proof discovery builds the canonical subgraph as it does now, then filters
`doubleCutElim` and single `vacuousElim` against the exact hits. Delete and
Backspace consume that filtered action list after the valid macro path. The game
context menu consumes the same discovery, so a suppressed single structural rule
is not displayed.

When structural elimination is inapplicable, the existing contextual order and
normalized-selection behavior of inconsistent-cut elimination, erasure, and
deiteration remain unchanged. No dispatcher may reconstruct a filtered structural
action later.

## Validation

Game interaction tests must prove:

- outer-cut-only and outer-plus-inner selections dispatch double-cut elimination;
- adding interior content suppresses double-cut elimination and reaches the next
  applicable rule;
- a single vacuous bubble dispatches trivial-quantifier elimination;
- adding interior content suppresses single trivial-quantifier elimination and
  reaches the next applicable rule;
- suppressed structural actions are absent from the game context menu;
- a valid multi-bubble chain still commits one deepest-first atomic action and
  clears selection once;
- invalid all-bubble macro selections retain their focused refusal;
- multiple bubble rims plus interior content bypass macro refusal and reach
  ordinary deletion.

Focused game controller tests, type checking, and the game worktree's complete
ordinary suite are authoritative.
