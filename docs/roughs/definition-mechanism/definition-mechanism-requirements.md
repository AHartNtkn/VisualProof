# Design brief: the relational definition/substitution mechanism

## The system (context)

A visual proof assistant for classical higher-order logic over untyped λ-terms,
in the existential-graphs tradition. Canonical reference: the approved spec at
/home/ahart/Documents/VisualProofAssistant/.worktrees/signature-indexed-wires/docs/superpowers/specs/2026-07-22-signature-indexed-wires-design.md
(read it first). Core laws, non-negotiable:

- Wires are identity/entities. A wire of sort ι is a line of identity over
  λ-terms; a wire of relational sort rel(σ⃗) IS a quantifier (∃ at even cut
  parity of its scope, ∀ at odd). Relations live on wires; nodes are assertions
  (assertion = presence in a region). Cuts are negation. No names, no textual
  labels in diagrams, ever — identity is connectivity, period.
- λ-term nodes assert the graph relation between their output and free-variable
  ports (y = t(x⃗)); spawning one with fresh wires is free because the closure
  is tautological (β-totality). Atoms apply a wire-borne relation: head port on
  the relation wire, arg ports on the arguments. Application is
  proposition-forming at relational sorts, hence contingent (gated).
- Backward proving is the default workflow (same calculus, polarity gates
  flipped by one boolean). Proof gestures are PRIMITIVES ONLY (user ruling):
  each step is one small visible move; no composite gestures.
- No comprehension-specific machinery may exist at any layer (user mandate):
  whatever mechanism handles relational definitions must be shared/uniform
  with how the rest of the system works, or derived from it.

## What was rejected

A "body node": sealed opaque disc carrying a nested content diagram, one output
port on the relation wire, unfold = splice-copy of the content at an atom.
Rejected because: no designed graphical interpretation (black box); substitution
is a teleport (content materializes elsewhere — no wire-mediated continuity;
the argument wires are missing from the definition object); "why singletons?"
has no answer (one exposed wire is an arbitrary corner of a family); and there
is NO equational theory for relational content — joining two definitions'
wires asserts their equality with no rules to discharge it even in trivially
true cases.

## The four requirements any design must satisfy

1. **Wire-mediated substitution with graphical continuity.** Instantiating a
   quantifier/occurrence through a definition must be a local, wire-mediated
   manipulation (argument-wire contact), like the term side's head strip /
   congruence / conversion — never a copy that materializes content at a
   distance.
2. **Drawn form derived from semantics.** Whatever carries a definition must
   have a graphical interpretation that follows from what it means — the way
   cuts mean negation and wires mean identity. No black boxes justified only
   by rendering convenience.
3. **The multi-wire family is the concept.** A definition mechanism should
   expose its content's coordinates as wires in a principled way — the
   spectrum from all-coordinates-exposed (the λ-node shape at ι) through
   partial applications — not privilege a single-wire corner case.
4. **An equational theory with real discharge power.** Relational content
   must be manipulable: content-level rewriting justified by equivalence
   proofs, and equality of definitions (asserted by joining their wires)
   dischargeable at least when contents are canonically isomorphic (α-level,
   free via the existing canonical-form machinery) and when equivalence is
   derivable (βη-level). Incompleteness may exist only where it must.

## Five sketched directions (starting points, freely combinable or discardable)

A. **Membrane**: definition = closed curve with the content drawn VISIBLY
   inside; boundary stubs cross the membrane as real wire-ends (the arg
   wires); membrane = graphical λ (holds structure apart from assertion);
   substitution = docking + membrane dissolution (curve deletes, wires zip).
B. **No carrier / build-in-place**: no definition object at all; instantiate
   per occurrence by generalizing/specializing one occurrence at a time
   (φ(G,G) ⊨ ∃R.φ(R,G) stepwise), with relational wire-joins reconciling the
   intermediate multiple quantifiers; equality discharge lives in the join.
C. **Unfold as docking**: keep a carrier but make the MOVE graphical:
   carrier transports along its identity wire to the atom, docks (boundary
   stubs zip pairwise with the atom's arg wires), dissolves into the merged
   content.
D. **Relations as closed curves**: a relational wire IS a closed curve; a
   defined relation is the curve with its definition drawn inside; atoms and
   arg wires attach at contact sites on the curve; substitution = sliding
   args along the curve into the interior. (Rebuilds wire physics around
   loops — highest risk/highest unification.)
E. **Equational layer (orthogonal)**: α-level equality free via canonical
   isomorphism; βη-level via proof-carrying content rewriting (a definition's
   content may be replaced by provably-equivalent content, justified by an
   ordinary two-directional sub-derivation on the content).
