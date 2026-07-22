# Double-Cut Delete Selection Design

**Status:** Approved
**Date:** 2026-07-22

## Outcome

Contextual Delete interprets the user's complete highlighted selection before it
chooses double-cut elimination. It may eliminate a double cut only when the exact
highlighted set is the outer cut alone or the outer cut together with its directly
nested inner cut. Any additional selected figure suppresses double-cut elimination
without changing the established order or semantics of the remaining deletion
rules.

## Selection Responsibilities

Proof discovery preserves two views of the same interaction:

- Exact hits are the renderer-owned set of semantic figures the user highlighted.
  They determine whether the selection expresses exclusive double-cut intent.
- The absorb-normalized `SubgraphSelection` remains the kernel-facing rule input.
  It continues to determine erasure, deiteration, wrapping, citations, and other
  proof moves.

These views are not competing semantic authorities. Exact hits answer whether a
UI gesture is eligible for one intent-sensitive candidate; the normalized
selection supplies the canonical subgraph to kernel rules.

## Discovery and Dispatch

`discoverProofActions` remains the shared boundary used by keyboard deletion and
the contextual action palette. It builds the normalized selection and enumerates
the ordinary actions as before, then retains `doubleCutElim` only when the exact
hits are one of these sets:

1. `{ outer cut }`
2. `{ outer cut, directly nested inner cut }`

The discovered outer cut must already satisfy the existing structural double-cut
gate. Hit order does not matter. A selected node, wire, bubble, unrelated cut, or
any third hit makes double-cut elimination inapplicable. No later dispatcher may
reintroduce that action.

When double-cut elimination is absent, contextual Delete continues with the
existing precedence: vacuous elimination, inconsistent-cut elimination, erasure,
then deiteration. Those candidates use the existing absorb-normalized selection.
The rule order itself is unchanged.

## Scope

The kernel double-cut applier remains unchanged because it owns structural rule
validity, not UI selection intent. Global `absorbHits` behavior also remains
unchanged because construction, copy, and other proof interactions rely on its
canonical subtree semantics. Only shared proof-action discovery gains the
intent-sensitive double-cut filter.

The prior regression assertion equating outer-cut-plus-interior-content with
outer-cut-only behavior is replaced. No compatibility path retains the looser
double-cut eligibility.

## Validation

Focused interaction tests must prove:

- outer cut alone discovers and dispatches double-cut elimination;
- outer plus its inner cut discovers and dispatches double-cut elimination;
- adding an interior node suppresses double-cut elimination and allows the next
  applicable contextual deletion;
- adding an interior wire or another interior region also suppresses the action;
- raw hit order does not change either accepted result;
- the contextual palette and Delete continue to consume the same discovery list.

The move tests, action tests, typecheck, and full non-physics suite must pass.
Source inspection must confirm that neither keyboard handling nor the contextual
palette constructs double-cut elimination after discovery has rejected it.
