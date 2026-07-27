# Capture-Only Theorem Citation Correction

**Status:** Phase-1 correction required by the Phase-2 reification proofs.

## Problem

A verified theorem may have an endpoint-free boundary wire on one side. Such a
wire is an ambient capture: it is part of the theorem's ordered interface, but
it is not incident to the occurrence content on that side. This is the exact
shape of the reification theorems:

```text
captures ⟹ Exists P. forall x. P(x) <-> G(x)
```

The theorem-application step already records both the selected occurrence
(`sel`) and one ordered host wire per theorem boundary position (`args`).
However, occurrence matching formerly accepted only host wires reported as
touching attachments by subgraph extraction. An endpoint-free capture cannot be
a touching attachment, so an ordinary citation of the theorem was impossible.

## Correct Model

The selected subgraph and the ordered arguments have distinct responsibilities:

- `sel` designates the occurrence content.
- `args[i]` designates the host wire for theorem boundary position `i`.
- If a theorem boundary wire has endpoints on the matched side, its argument
  must be a touching attachment of the selected content.
- If a theorem boundary wire has no endpoints on the matched side, it is an
  ambient capture. Its argument is supplied directly by `args[i]`; no selected
  incidence is required.
- Every touching attachment of the selected content must still occur in
  `args`.

The matcher constructs the complete candidate boundary and compares its pinned
canonical form with the theorem side. Candidate boundary positions reuse the
same stub exactly when their host arguments name the same wire. Consequently:

- ordered signatures must match;
- distinct theorem boundary identities cannot be silently diagonalized onto
  one host wire;
- a repeated theorem boundary identity cannot be split across different host
  wires;
- content incidence and ambient-capture aliases remain exact.

After matching, the existing splice remains authoritative for host-wire
existence, signature equality, scope enclosure, and boundary connection. The
splice is performed with the same ordered `args`, and only the selected content
is removed.

## Scope

This correction changes only ordinary theorem-side occurrence matching. It does
not add a proof step, alter proof JSON, change theorem data, modify kernel
logical rules, change relation quantifiers, or create a Phase-2 proof
authority.
