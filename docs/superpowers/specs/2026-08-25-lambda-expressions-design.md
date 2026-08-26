# Lambda Expressions Design

**Status:** Approved on 2026-08-25

## Goal

Restore Lambda expressions to the signature-indexed-wire implementation, including
the complete main-branch interaction surface, formula entry, proof replay, 2D and
3D rendering, and structurally animated beta reduction. The implementation starts
from `worktree-signature-indexed-wires` and uses
`/home/ahart/Documents/gameProj/demos/lambda_tromp_reduction_demo_corrected.html`
as the reduction-animation authority.

## Authorities

- `main` supplies the existing Lambda term calculus and user interactions.
- `worktree-signature-indexed-wires` supplies the diagram, signature, wire,
  identity, proof-step, rendering, and Lean architecture into which Lambda terms
  are restored.
- The corrected Tromp demo supplies the reduction geometry, stage ordering,
  incidence tracking, and color tracking.

## Term representation

The term calculus is nameless. Its structural forms are:

```text
Term ::= bound(index) | free(slot) | lambda(body) | application(fn, arg)
```

Bound occurrences use de Bruijn indices. Free occurrences use an ordered,
canonical interface of slots. Identifiers accepted by text input exist only while
parsing and printing; they do not enter diagram equality, rule evidence, replay,
or Lean semantics.

A Lambda expression is one whole term. Lambda terms contain no definition form.
Definitions are relations.

The existing parser, printer, serializer, path operations, capture-avoiding
substitution, beta and eta reduction, normalization, head normalization, and
conversion-certificate checker return as the term subsystem.

## Diagram representation

Add a `term` diagram node to the signature-indexed graph. It owns:

- one complete nameless `Term`;
- one ordered canonical free-slot interface;
- one `output` port accepting `IOTA`; and
- one `free` port accepting `IOTA` for each interface slot.

All term-node ports participate in the same endpoint validation, derived wire
scope, two-end wire floor, canonical labeling, occurrence matching, extraction,
splicing, JSON serialization, and proof replay as existing diagram nodes.

Term structure and the ordered free-slot interface are canonical node content.
Free-slot storage labels do not survive canonical comparison as semantic names.
Term alpha-equivalence is structural because bound variables are indices.

## Propositional formula entry

Every completed diagram is a proposition. Formula syntax admits whole Lambda terms
in relation arguments and equality operands. The symbol palette includes `λ`, and
the textual parser also accepts the established ASCII abstraction syntax.

Formula parsing resolves source binders into de Bruijn indices or bound diagram
wires and produces term operands. Formula translation:

- connects a simple bound operand directly to its existing wire;
- draws a term node for an abstraction, application, or explicit free-term node;
- connects each term-node free port to the corresponding enclosing individual
  wire; and
- connects the term-node output to the relation argument or equality incidence
  that consumes the term.

Formula validation rejects non-individual terms in individual positions, unbound
formula inputs, malformed binders, and signature mismatches with source spans.

## Lambda rules

TypeScript Lambda rule implementations live under a dedicated
`src/kernel/rules/lambda/` module. Lean Lambda rule declarations live in
`VisualProof/Rule/Lambda.lean`, with their soundness work under
`VisualProof/Rule/Soundness/Lambda/`. The public rule and step aggregators import
those modules.

### Conversion

Conversion replaces one term node with a beta-eta-convertible whole term. The rule
uses an explicit correspondence between the old and new free-slot interfaces and
preserves the term output incidence. Interactive execution may search under a fuel
budget; replay checks the stored certificate without fuel.

Normalization, head normalization, weak-head normalization, double-click
normalization, and custom conversion are clients of this rule.

### Free-variable identity

A dedicated bidirectional Lambda rule converts:

```text
term node containing exactly free(slot 0)
    output wire: a
    free-slot wire: b
```

to:

```text
binary IOTA identity node incident to a and b
```

and back while preserving those two wires. Every binary `IOTA` identity is a
valid reverse source. Because identity incidence is unordered, reverse execution
enumerates the distinct output/free-slot orientations and removes isomorphic
duplicates. The construction introduces no variable name.

### Existing term operations

Restore the main-branch term-node operations required by its interaction surface,
including term spawning, term conversion, term fission/copy behavior, subterm hit
testing, connection behavior, proof action encoding, composition, JSON replay,
and persistence.

## Spawning and interaction

The ordinary still-right-click construction cascade contains an entry labeled
`Lambda expression`. Selecting it opens Lambda input at the captured region and
pointer position. Enter commits through the existing edit or proof pipeline, and
parse or rule refusal leaves the editor open with the existing feedback behavior.

A spawned term node receives one fresh wire per port. Every such fresh wire is
capped by a unary `IOTA` identity node, including the output wire and each free-slot
wire. This satisfies the current diagram's two-end floor and retains all of the
term node's incidences for later connection.

The restored surface includes placement, selection, subterm targeting, dragging,
copying, fission, connection, undo/redo, history preview, replay, and persistence.

## Two-dimensional rendering

The Lambda painter draws the bent Tromp incidence diagram used by the main branch:

- abstractions are circular arcs;
- applications are transverse connectors;
- bound-variable occurrences connect structurally to their binder arcs;
- free slots and the result connect to the term node's external ports; and
- layout is derived from term structure rather than displayed binder names.

Term hit testing and subterm selection use the same generated geometry as painting.

## Three-dimensional rendering

The 3D renderer embeds the same Lambda strokes in a circular local plane. That
plane is perpendicular to the diagram branch direction at the term node. The
figure has no filled surface: its disk-like character is the planar circular
footprint of its line geometry.

The base stroke color is the authoritative term-wire color in both light and dark
themes. Picking, hover, focus, camera framing, and transitions operate on the
Lambda strokes and their incident term wires.

## Reduction animation

Each beta step builds a structural correspondence between the pre-reduction and
post-reduction term models. Persistent junctions move continuously. Consumed
strokes are explicitly classified, and every introduced stroke must belong to a
complete copy of the argument.

For a used binder, normalized transition time uses the corrected-demo boundaries:

```text
identify  0.000–0.150
duplicate 0.150–0.340
make space 0.340–0.540
substitute 0.540–0.820
cleanup   0.820–0.965
settle    0.965–1.000
```

For an unused binder:

```text
identify 0.000–0.150
discard  0.150–0.380
make space 0.380–0.640
cleanup  0.640–0.930
settle   0.930–1.000
```

The redex transitions from the base term-wire color to the redex color. The
argument transitions to the argument color. Complete copies separate before
substitution and receive the corrected-demo repeating copy hues. Those hues remain
attached to subterm lineage while copies move and reshape, then return to the base
term-wire color during settle. The same motion plan and color lineage drive 2D and
3D rendering.

## Lean formalization

Restore the nameless Lambda syntax, renaming, substitution, reduction,
normalization, quotient, certificates, and normal-separation results under
`VisualProof/Lambda/`, adapted to the current signature-indexed diagram model.

Extend diagram nodes, ports, well-formedness, renaming, isomorphism, semantics, and
open-diagram machinery for term nodes. Add the Lambda conversion and free-variable
identity relations and prove their soundness. Register their evidence in the
public step relation and replay surface.

Lean work follows theorem-driven RED/GREEN development. Definitions in a theorem's
dependency closure are complete before RED. The owning production theorem may use
`sorry` for RED and is completed with a kernel-checked proof for GREEN.

## Validation

Behavioral validation includes:

- unit tests for parsing, printing, serialization, substitution, reduction,
  normalization, certificates, and nameless invariants;
- formula tests for Lambda terms in relation arguments and equality operands;
- diagram tests for signatures, validation, canonicalization, isomorphism,
  occurrence matching, extraction, splicing, and JSON round trips;
- rule tests for conversion and both directions of free-variable identity;
- interaction and end-to-end tests for right-click entry, unary caps, placement,
  normalization, undo, replay, and persistence;
- 2D and 3D geometry, hit-testing, color, and transition tests; and
- `npm test`, `npm run typecheck`, `npm run e2e`, and `lake build`.

Rendered validation must exercise actual application output in both 2D and 3D and
compare it against the corrected demo for at least:

1. `(\x. x) a` — one substitution;
2. `(\f. \x. f (f x)) (\z. z)` — duplication;
3. `(\x. kept) ((\z. z) discarded)` — deletion;
4. `(\x. \y. x y) (\w. w)` — nested binder; and
5. `(\x. \y. x) y` — capture avoidance.

The comparison covers geometry, stage boundaries, structural motion, and color
tracking. Passing source tests or static snapshots alone is insufficient.
