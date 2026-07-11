# Bound-Predicate Spawn Design

**Status:** Approved  
**Date:** 2026-07-10

## Outcome

The existing contextual spawn cascade exposes predicate atoms bound by quantifier bubbles at the invocation point. The interaction makes nested binder choice visually obvious while preserving the kernel's single authoritative binder model.

## Construction vocabulary

The cascade derives two distinct kinds of predicate-like choice:

- Named relations come from the loaded verified relation library and create reference nodes.
- Bound predicates come from bubble regions on the invocation region's ancestor chain and create atom nodes.

Bound-predicate entries are ordered from the innermost eligible bubble outward. With one eligible bubble, the cascade shows one direct `Bound predicate /n` entry. With `k` nested eligible bubbles, the entries are labeled `Binder 1 (innermost)`, `Binder 2`, …, `Binder k (outermost)`, each with its `/n` arity hint. Internal region identifiers are never user-facing.

When no bubble encloses the invocation region, the bound-predicate section is absent. Bound predicates do not participate in named-relation search results or named-relation recents.

## Visual disambiguation

Each bound-predicate entry has a small filled circle using the same authoritative hue as its binder bubble and existing atom occurrences. The cascade does not store or calculate a second semantic color; it receives presentation color derived from the diagram's established binder-hue mapping.

Hovering an entry temporarily highlights its binder bubble on the diagram using the existing binder-group highlight language. This emphasis is view-only. It begins on entry hover and clears on pointer leave, cascade close, entry selection, outside dismissal, Escape, replacement by a newly opened cascade, or disposal.

Color is not the sole disambiguator: nesting label, arity, ordering, and hover emphasis all identify the target binder.

## Semantic edit

Selecting a bound-predicate entry submits the exact binder identity and the immutable spawn invocation. The application creates one atom whose:

- region is the invocation region;
- binder is the selected enclosing bubble;
- argument ports are derived from that bubble's current arity; and
- singleton argument wires are scoped to the invocation region.

The atom stores no copied arity, name, or color. The validated diagram constructor remains responsible for rejecting a missing, non-bubble, or non-ancestor binder.

The accepted edit travels through the existing edit-history, diagram synchronization, and body-placement path, so ordinary undo and click-local placement work exactly as for term and named-relation spawns. A refused edit leaves the cascade open and surfaces the existing pointer-local refusal feedback.

## Ownership

- The kernel diagram owns binder identity, bubble arity, atom ancestry, required ports, and structural validation.
- The spawn catalogue owns deterministic discovery and ordering of eligible binders.
- The cascade owns menu DOM and hover lifecycle, but no diagram or renderer state.
- The application shell owns transient binder emphasis and commits accepted edits through the existing edit transaction.
- The renderer remains the sole source of binder color and highlight geometry.

There is no separate predicate palette, global binder-selection mode, remembered binder state, copied atom arity/color, or renderer-only predicate representation.

## Validation

Automated validation must prove:

1. No enclosing bubble yields no bound-predicate option.
2. One enclosing bubble yields one direct option with its identity and derived arity.
3. Nested bubbles yield one option per enclosing bubble, innermost first.
4. Atom construction records the chosen binder, creates every derived argument port exactly once, and scopes new wires to the invocation region.
5. A binder outside the invocation region's ancestor chain is rejected by authoritative diagram validation.
6. The cascade renders the binder-colored circle, dispatches the exact binder, and requests/clears hover emphasis for every closing path.
7. Named-relation search, recents, and spawning remain separate and unchanged.
8. The actual application can right-click within a bubble, choose its bound predicate, inspect a semantically bound atom, and undo the edit.

Only focused application, kernel-adjacent construction, type-check, and relevant end-to-end checks are required. Physics tests are excluded because this design changes no physics responsibility.
