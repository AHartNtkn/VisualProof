# Anchored Wire Rules Design

**Date:** 2026-07-11  
**Status:** Written for final review

## Outcome

Replace the specialized `endpointTransport` primitive with two general,
polarity-blind wire equivalences: anchored wire split and anchored wire
contraction. The pair preserves every transport derivation, including equality
available only locally behind a cut, and extends the calculus to arbitrary
endpoint groups and non-co-resident witnesses.

The kernel and theorem migration is implemented first. Later application
integration must use the same wire severing and joining interaction
implementations in Edit and Prove; their applicability and commit policies may
differ, but gesture capture, hit testing, configuration, previews, and
cancellation may not. Anchored split's explicit target region is a material
operand and will be visually evaluated before that integration rather than
silently inferred here.

## Witness availability

For a closed term witness node `n` whose output is on wire `w`, define
`anchorAvailability(d, n)` as the outermost ancestor `A` of `n.region` such
that:

- `A` is at or inside `w.scope`; and
- `cutDepth(A) === cutDepth(n.region)`.

Operationally, walk outward from `n.region` through bubbles and other
cut-depth-preserving parent transitions, stopping before crossing a cut or
leaving `w.scope`.

The returned region is the outer boundary of where the equation
`w = ⟦n.term⟧` is available. It propagates outward through bubbles because the
term is closed and cannot mention the bubble's bound relation. It propagates
inward through arbitrary descendants, including cuts.

The helper rejects a non-term witness, an open term, or a node whose output is
not carried by a valid wire. It is the sole availability authority used by both
rules and their application policies.

## Anchored wire split

The proof step is:

```ts
{
  rule: 'anchoredWireSplit'
  wire: WireId
  witness: NodeId
  endpoints: readonly Endpoint[]
  target: RegionId
}
```

It is valid when:

1. `witness` is a closed term node whose output is on `wire`.
2. `target` is at or inside `anchorAvailability(d, witness)`.
3. Every selected endpoint exists on `wire`, is not the witness's output, and
   its node lies at or inside `target`.
4. The endpoint list contains no duplicate semantic endpoint.

The rule:

1. leaves the original wire and witness in place;
2. creates one fresh wire scoped at `target`;
3. moves the selected endpoints from the original wire to the fresh wire; and
4. creates an identical closed term witness in `target`, with its output on the
   fresh wire.

The empty endpoint group is allowed: it creates a separately quantified copy
of the same closed value. Moving every non-witness endpoint is also allowed.

The duplicate is always placed in `target`. Placing it deeper would not anchor
the fresh wire throughout its declared scope.

## Anchored wire contraction

The proof step is:

```ts
{
  rule: 'anchoredWireContract'
  redundant: NodeId
  survivor: NodeId
  certificate: ConversionCertificate
}
```

`redundant` and `survivor` name the witness nodes; their output wires are
derived authoritatively.

It is valid when:

1. Both witnesses are distinct closed term nodes on distinct output wires.
2. Replaying `certificate` proves their terms βη-equal.
3. The redundant witness is globally available on its wire:
   `cutDepth(redundantWire.scope) === cutDepth(redundant.region)`.
4. Every non-redundant-witness endpoint on the redundant wire has a node at or
   inside `anchorAvailability(d, survivor)`.

The rule moves every non-witness endpoint from the redundant wire to the
survivor wire, then deletes the redundant witness and redundant wire. The
survivor wire's scope, identity, witness, and existing endpoints remain.

The survivor availability condition implies that its wire scope encloses every
moved endpoint. The explicit availability check remains the semantic gate; the
diagram well-formedness check is not a substitute.

## Hard soundness boundaries

### Endpoints outside availability

For root-scoped `w`, root consumer `P(w)`, and witness `w = 0` inside a cut,
the original means:

```text
∃x (P(x) ∧ ¬(x = 0))
```

Splitting `P` to a fresh root-visible wire while duplicating the witness inside
the cut yields:

```text
∃x∃y (P(y) ∧ ¬(x = 0 ∧ y = 0))
```

In a two-element domain with `P = {0}`, the original is false and the result
true. Therefore split targets and moved endpoints must stay inside witness
availability.

### Shielded contraction source

Deleting a source quantifier requires the source witness to anchor its wire at
the wire's own scope. In general:

```text
∃x ¬(x = 0 ∧ A)
```

is not equivalent to `¬A`. Consequently contraction cannot consume a witness
shielded from its wire scope by a cut, even if the survivor witness is locally
available to all moved endpoints.

These gates are fixed semantic boundaries, not configurable conservatism.

## Deriving local endpoint redistribution

Every former `endpointTransport(a, b, endpoint, certificate)` is derived as:

1. Let `R` be a region inside `anchorAvailability(a)` that encloses the moved
   endpoint node. Apply `anchoredWireSplit` to `a`'s output wire with
   `endpoints: [endpoint]` and `target: R`. This creates a locally unshielded
   duplicate witness `aCopy` on a fresh `R`-scoped wire.
2. Apply `anchoredWireContract` with `redundant: aCopy`, `survivor: b`, and the
   original certificate. The fresh wire is contractible because its witness
   and scope are co-located; `b`'s availability covers the endpoint.

The same derivation moves any endpoint subset. The witnesses need not be
co-resident: their availability regions need only support the chosen split
target and moved endpoints.

For equality entailed behind a cut, choose the evidence region as the split
target. Both original wires retain their scopes and identities, so the pair
strictly subsumes the specialized transport rule.

## `zeroIsNat` migration

The production derivation uses the shorter unshielded route:

1. Split the conclusion predicate endpoint from the internally anchored `w0`
   at the guard bubble. The duplicate internal ZERO witness anchors the fresh
   local wire.
2. Contract that fresh wire directly into the external `wz` wire using the
   unshielded root witness `zExt`.

The iterated external witness copy and its later deiteration disappear. `w0`
never changes scope and retains the internal ZERO witness and base predicate.
The conclusion alone moves to `wz`, leaving the exact non-vacuous
`natRelation(z)` shape required by `relFold`.

A separate kernel test derives the former shielded-copy route to prove that the
new pair preserves the full old capability rather than only the production
theorem's shorter path.

## Shared interaction constraint

This kernel replacement does not add an application entrance. It establishes
the following constraints for the later interaction design:

- Endpoint-group capture must reuse the existing sever gesture implementation,
  including right-drag slash, the configured double-click alternative,
  endpoint hit resolution, preview, and cancellation.
- Wire contraction must reuse the existing wire drag-to-wire implementation,
  including target hit testing and the green pointer/target preview.
- `anchoredWireSplit.target` is not inferred by the kernel and is not an
  invisible justification choice. Different target scopes produce different
  diagrams, so the player-facing interaction must author or unambiguously
  indicate it.
- Witness or certificate choices that produce exactly the same resulting
  diagram may be resolved canonically without user interaction.
- No proof-only sever controller, duplicate wire-drag controller, or
  endpoint-specific tool may be introduced.

The move-by-move visual evaluation will select the target-region affordance
before application integration is planned or implemented.

## Displaced model

Remove rather than retain or alias:

- the `endpointTransport` `ProofStep` variant and dispatch;
- its rule applier and rule export;
- JSON serialization and parsing cases;
- composition/remapping cases;
- specialized tests and fixtures after their capability assertions migrate;
- theory and generated-example steps;
- documentation describing transport as a primitive;
- any proposed endpoint-specific UI interaction.

No deprecated JSON reader, compatibility step, wrapper, macro named
`endpointTransport`, or fallback path remains.

## Validation

Focused tests must prove:

1. Availability crosses nested bubbles, stops at the first cut, never leaves
   the witness wire's scope, and is invariant under IDs.
2. Split accepts targets at and below availability, arbitrary endpoint groups,
   empty/all-non-witness groups, and either proof orientation.
3. Split rejects targets outside availability, endpoints outside target,
   duplicate/unknown endpoints, the witness output, open witnesses, and wrong
   witness wires.
4. The duplicate witness is created exactly in `target` and the fresh wire is
   scoped exactly there.
5. Contraction accepts βη-equal closed anchors with moved endpoints inside
   survivor availability, including witnesses in different regions.
6. Contraction rejects a shielded redundant witness, an endpoint just outside
   survivor availability, open or non-term witnesses, rejected certificates,
   identical witnesses, and shared output wires.
7. Split followed by contraction returns the exact original diagram on the
   inverse domain.
8. Split plus contraction produces the exact former transport result for one
   and many endpoints, including shielded co-resident witnesses.
9. Strict JSON round-trip/rejection and non-identity proof composition remap all
   step IDs and endpoints.
10. Removing either hard gate, changing duplicate placement, skipping
    certificate replay, or weakening closedness makes a named mutation test
    fail.
11. `zeroIsNat`, the full Frege theorem battery, and generated JSON verify; the
    internal base wire remains bubble-scoped and the obsolete copy/deiteration
    pair is absent.
12. Repository searches find no production `endpointTransport` path.

Run focused kernel tests first, then the full non-physics suite, type checking,
theory generation, and theorem verification. Browser interaction tests belong
to the separately approved application-integration plan.
