# Arithmetic induction carriers

**Status:** Authoritative correction for the relational Frege rebuild.

## Changelog

- 2026-07-26: Replaced four assertion-shaped carriers with the exact
  countermodel-backed induction invariants below. In particular, right identity
  also requires correction; the earlier assertion can hold vacuously without
  addition totality.

## Boundary

This note fixes the unary relations reified for the four arithmetic induction
proofs. It does not add a kernel rule, change proof JSON, change an arithmetic
theorem statement, or make a reification theorem into a definition or spawn
authority.

Each carrier is ordinary explicit relation material recorded by the existing
sequence:

```text
strongest relation grounding -> iteration -> strongest relation severing
```

The resulting reification fact is an ordinary theorem. Second-order
substitution remains the derived reification-plus-iteration construction.

## Right identity

Capture order:

```text
Zero, Plus
```

Carrier:

```text
E(a) := forall z. Zero(z) -> Plus(a,z,a)
```

The previously recorded predicate

```text
forall z,o. Zero(z) and Plus(a,z,o) -> o=a
```

is not a valid induction invariant under the seven standing hypotheses. It may
hold vacuously at `a` when no `Plus(a,z,_)` instance exists, then fail at
`Successor(a)`. A four-element countermodel realizes exactly this case while
satisfying the standing hypotheses.

`E` is the minimal carrier. Addition base proves its base case, addition step
proves hereditary closure, and Plus functionality converts the final
`Plus(a,z,a)` fact and the theorem premise `Plus(a,z,o)` into `o=a`.

## Associativity

Capture order:

```text
Plus
```

Carrier:

```text
A(a) :=
  (forall b. exists t. Plus(a,b,t))
  and
  (forall b,c,t,u.
    Plus(a,b,t) and Plus(b,c,u)
    -> exists v. Plus(t,c,v) and Plus(a,u,v))
```

The totality conjunct supplies the outputs needed by the hereditary step. The
transport output `v` is existential inside the implication consequent; it is
proof-local and is not the public associativity statement's intermediate
wire.

The prior already-composed assertion is not hereditary without Plus totality.
A four-element countermodel satisfies the seven hypotheses while that
predicate holds at one element and fails at its successor.

## Successor shift

Capture order:

```text
Successor, Plus
```

Carrier:

```text
S(a) :=
  (forall b. exists t. Plus(a,b,t))
  and
  (forall b,sb,t,st.
    Successor(b,sb) and Plus(a,b,t) and Successor(t,st)
    -> Plus(a,sb,st))
```

The forward implication alone is insufficient: its hereditary proof requires
the totality output that becomes the predecessor sum.

## Commutativity

Capture order:

```text
Plus, r
```

Carrier:

```text
C_r(a) :=
  (forall b. exists t. Plus(a,b,t))
  and
  (forall o. Plus(a,r,o) -> Plus(r,a,o))
```

The addend `r` is a fixed individual capture, not a variable quantified inside
the carrier. This is the invariant proved while inducting on `a`. Totality
supplies the outputs required by the successor step.

## Required validation

Carrier validation must establish all of the following directly:

- exact capture signatures and order;
- totality inputs are universal and outputs existential;
- associativity's `v` is existential in the transport consequent;
- right identity contains `Plus(a,z,a)`, not a vacuity-prone equality
  assertion;
- commutativity fixes `r` at the theorem boundary;
- each theorem replays without refs, `refSpawn`, unfold/fold shortcuts, or a
  privileged definition;
- each theorem contains exactly one indispensable strongest-form relation
  sever;
- consumers use strongest-form grounding and do not expose helper carrier
  theorems in the public arithmetic suffix.
