# Checked Concrete Elaboration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Compute the existing intrinsic `Region signature 0 []` from every checked finite concrete diagram, define concrete denotation only through that intrinsic result, and prove the result invariant up to the existing intrinsic `Core.Isomorphic` relation under concrete identifier isomorphism.

**Architecture:** One private proof-independent `Option` kernel computes from raw finite data. `ConcreteDiagram.WellFormed` proves that kernel succeeds; it contributes no output data and remains the sole validation authority. Elaboration allocates every wire at its declared lexical scope, threads ambient wire and bubble-binder contexts, and deterministically enumerates local node/child occurrences. Concrete identifier order may choose an intrinsic representative, so invariance is `RegionIso`, not equality or pre-elaboration canonicalization.

**Comparative evidence:** `../diagegraph` supports explicit component bijections, preservation laws, and separation of declarative isomorphism from executable canonicalization. Its exhaustive permutation/orbit canonicalizer is intentionally deferred to the exact matcher: it is unnecessary and factorial for checked elaboration.

**Tech Stack:** Lean 4.30.0, Std only, existing concrete graph foundation, intrinsic `Region`, `FiniteEquiv`, `RegionIso`, and intrinsic semantics.

## Global Constraints

- Lean development is theorem-driven. A transient `sorry` may mark a correctly stated theorem while its proof is being developed; no `sorry`, `admit`, or project axiom may remain at review or commit.
- `ConcreteDiagram.WellFormed` and `checkWellFormed` remain the sole validation authority. The partial construction kernel is private and must not become a public validator or error model.
- The computed intrinsic value depends only on raw finite graph data. Never eliminate a `Prop` witness to choose output data; use well-formedness only to prove private failure unreachable.
- Preserve lexical wire scope and endpoint-less bare wires. Preserve ordered port indices and concrete bubble identity. Treat endpoint-list order and item enumeration order as nonsemantic.
- Do not add a second diagram syntax, canonical representation, fallback empty region, classical witness selection, or exhaustive identifier canonicalizer.
- If the traversal gate reveals that the approved `WellFormed` contract is insufficient, stop implementation and replace the foundation record before changing the public model.
- Validation is focused/full elaboration, theorem axiom inspection, forbidden-authority scan, representative computation theorems, and independent review.

---

### Task 1: Executable finite support and traversal gate

**Files:**
- Create: `VisualProof/Diagram/Concrete/Elaboration/Finite.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration/Traversal.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** Complete/nodup `Fin` enumeration and filtering, executable finite search/sequencing, exact-scope wire and local-occurrence enumerations, and the isolated theorem that a checked rooted parent graph cannot exhaust `regionCount`-bounded descent.

- [x] Define a canonical `List (Fin n)` enumeration, predicate filtering, index lookup, and `sequenceFin`, with soundness/completeness/nodup theorems.
- [x] Define exact-scope wire enumeration and tagged local occurrences (`node` or direct child region) as compiler-private references, not syntax.
- [x] State the fuel/no-exhaustion theorem before proving it. Derive it from `AllRegionsReachRoot`, unique total parent data, and finiteness.
- [x] If the proof requires a cleaner recursion state, replace fuel internally with a remaining-region list. Do not add a runtime fallback or strengthen `WellFormed` without a new foundation decision.
- [x] Build the focused modules and inspect their theorem axioms.
- [x] Commit the traversal gate independently.

---

### Task 2: Lexical environments and total checked lookups

**Files:**
- Create: `VisualProof/Diagram/Concrete/Elaboration/Context.lean`
- Modify: `VisualProof/Diagram/Concrete/Elaboration.lean`

**Produces:** Executable ambient-wire and binder contexts, endpoint-owner lookup, ordered port resolution, named-reference lookup, and all checked success/uniqueness lemmas needed by the kernel.

- [ ] Represent ambient concrete wires by an indexed enumeration synchronized with intrinsic `Fin wires`; extend it by the current exact-scope local-wire fiber using outer-prefix/local-suffix layout.
- [ ] Represent active bubbles in de Bruijn order with concrete region identity and arity; prove entering a bubble produces the head `RelVar` and lifts existing binders.
- [ ] Define private finite endpoint-owner lookup and prove coverage plus disjointness/nodup give the unique incident wire for every required port.
- [ ] Prove `WireScopesEnclose` makes every resolved node port active in its lexical wire environment.
- [ ] Prove `AtomBindersAreBubbles` and `AtomBindersEnclose` make the exact concrete binder available with its arity; prove named lookup succeeds from `NamedReferencesResolve`.
- [ ] Build and inspect theorem axioms; commit independently.

---

### Task 3: Sole private kernel, checked total API, and denotation

**Files:**
- Create: `VisualProof/Diagram/Concrete/Elaboration/Compile.lean`
- Create: `VisualProof/Diagram/Concrete/Semantics.lean`
- Modify: `VisualProof/Diagram/Concrete/Elaboration.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** Private proof-independent elaboration, public total checked elaboration, proof irrelevance/computation theorems, and concrete denotation only through intrinsic semantics.

- [ ] Implement the private recursive `Option` kernel. At each region enumerate every exact-scope wire (including bare wires), extend the wire environment, translate local nodes, and recurse over direct children.
- [ ] Translate terms to equations using output resolution and `Lambda.Term.mapFree`; translate atoms by exact binder identity and ordered `.arg`; translate named relations using checked signature lookup and ordered `.arg`.
- [ ] State and prove recursive success under the traversal/context invariants, then root success from `WellFormed`.
- [ ] Expose only a total API from `CheckedDiagram signature` (plus the equivalent diagram/proof equation if useful). Prove the output is independent of proof witnesses and state its computation equation against the private kernel.
- [ ] Define concrete denotation by applying existing intrinsic denotation to the elaborated region. Do not duplicate semantic clauses.
- [ ] Add theorem-owned examples covering the valid nested diagram and the bare-wire diagram; build, inspect axioms, scan for alternate authorities, and commit.

---

### Task 4: Declarative concrete identifier isomorphism

**Files:**
- Create: `VisualProof/Diagram/Concrete/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** `ConcreteIso` with region/node/wire `FiniteEquiv`s; preservation of root, region/node structure, wire scopes, and endpoint incidence; `refl`, `symm`, `trans`; and transport of every well-formedness invariant.

- [ ] Define endpoint renaming by node equivalence while leaving `CPort` unchanged.
- [ ] Define `ConcreteIso` over raw diagrams. Region laws preserve kind, mapped parent, and bubble arity; node laws preserve constructor, mapped locations/binders, terms, named definitions/arities; wire laws preserve mapped scope and endpoint membership.
- [ ] Use bidirectional endpoint membership (or mapped `List.Perm`) so order is nonsemantic while nodup remains transportable. Never require endpoint-list equality.
- [ ] Prove `ConcreteIso.refl`, `.symm`, `.trans` and transport all eleven named invariants, then `WellFormed` and `CheckedDiagram`.
- [ ] Add a nontrivial identifier-permutation witness and prove its checked transport; build, inspect axioms, and commit.

---

### Task 5: Elaboration equivariance into intrinsic isomorphism

**Files:**
- Create: `VisualProof/Diagram/Concrete/Elaboration/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Concrete/Elaboration.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** The main theorem that concretely isomorphic checked diagrams elaborate to `Core.Isomorphic` intrinsic regions, hence have identical denotation.

- [ ] Prove exact-scope wire filtering respects concrete wire equivalence and construct the restricted local `FiniteEquiv`.
- [ ] Prove ambient wire extension commutes with concrete renaming via existing `extendWireEquiv`; prove port resolution is equivariant.
- [ ] Prove binder contexts agree along corresponding region paths and all node translations yield the required intrinsic `ItemIso`.
- [ ] Restrict node/child equivalences to tagged local-occurrence fibers and combine them into the position equivalence used by `ItemSeqIso.permute`.
- [ ] Prove the synchronized recursive worker theorem and derive:

```lean
theorem ConcreteIso.elaborate_isomorphic
    (iso : ConcreteIso d e)
    (hd : d.WellFormed signature)
    (he : e.WellFormed signature) :
    Core.Isomorphic (d.elaborate hd) (e.elaborate he)
```

- [ ] Derive concrete denotation invariance from existing `Core.iso_denotation` rather than reproving semantics.
- [ ] Prove the nontrivial permutation example, build focused/full project, inspect all public theorem axioms, scan forbidden tokens/alternate authorities, and commit.

---

### Task 6: Independent integration review

**Files:**
- Modify only defects found in Tasks 1-5 and the umbrella imports.

- [ ] Review the implementation against the approved hybrid architecture, the concrete foundation, and this plan.
- [ ] Verify no public partial elaborator, second validator, canonical graph, default result, proof-chosen data, scope flattening, or endpoint-order semantics remains.
- [ ] Run `lake build`; inspect axioms of totality, proof irrelevance, concrete-isomorphism transport, elaboration isomorphism, and denotation invariance.
- [ ] Append the foundation record's `<conformance>` section with ownership, replacement, migration, and validation evidence.
