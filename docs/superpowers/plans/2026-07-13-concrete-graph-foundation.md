# Concrete Graph Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define VisualProof's normalized total finite graph, its complete well-formedness proposition, and one structured checker proved to accept exactly the well-formed graphs.

**Architecture:** Concrete identifiers are separate finite types and all ownership tables are total, so absent identifiers are unrepresentable. The graph remains extrinsic exactly where malformed semantic states must be diagnosed: region parent structure, binder kind/enclosure, contextual named-reference resolution, endpoint ports and incidence, and wire scope. One `WellFormed` proposition owns those obligations; one `Except` checker decides it.

**Tech Stack:** Lean 4.30.0, Std only, existing `VisualProof.Lambda.Syntax`, existing `VisualProof.Diagram.Isomorphism` only where finite equivalences are needed later.

## Global Constraints

- Lean proof development is theorem-driven, not test-driven. State each named theorem before its proof; a transient `sorry` is permitted only while proving that statement, and no admission may remain at review or commit.
- Do not add separate Lean test modules for propositions already expressed by named theorems.
- Region, node, and wire identifiers use `Fin`; do not add string identifiers, partial maps, or a parsing model.
- The checker and `WellFormed` are the sole validation authority. Do not add a Boolean validator, normalization constructor, wrapper, or unchecked checked-diagram path.
- Endpoint-list order is not semantic. Duplicate occurrences are invalid, while an empty endpoint list is a valid bare wire.
- Named references resolve against `signature : List Nat`; graph-level data stays independent of a particular signature.
- Final validation is focused/full elaboration, theorem axiom inspection, forbidden-token/alternate-authority scan, and independent review.

---

### Task 1: Total finite graph data and decidable structural predicates

**Files:**
- Create: `VisualProof/Diagram/Concrete/Core.lean`
- Create: `VisualProof/Diagram/Concrete.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `VisualProof.Lambda.Syntax`.
- Produces: `CRegion`, `CPort`, `CEndpoint`, `CNode`, `CWire`, `ConcreteDiagram`, `OpenConcreteDiagram`, bounded parent traversal, `Encloses`, required-port predicates, and decidability for every later invariant.

- [ ] **Step 1: Declare the normalized graph data**

```lean
inductive CRegion (regions : Nat)
  | sheet
  | cut (parent : Fin regions)
  | bubble (parent : Fin regions) (arity : Nat)
  deriving DecidableEq

inductive CPort
  | output
  | free (index : Nat)
  | arg (index : Nat)
  deriving DecidableEq

structure CEndpoint (nodes : Nat) where
  node : Fin nodes
  port : CPort
  deriving DecidableEq

inductive CNode (regions : Nat)
  | term (region : Fin regions) (freePorts : Nat)
      (term : Lambda.Term 0 (Fin freePorts))
  | atom (region binder : Fin regions)
  | named (region : Fin regions) (definition arity : Nat)

structure CWire (regions nodes : Nat) where
  scope : Fin regions
  endpoints : List (CEndpoint nodes)

structure ConcreteDiagram where
  regionCount : Nat
  nodeCount : Nat
  wireCount : Nat
  root : Fin regionCount
  regions : Fin regionCount -> CRegion regionCount
  nodes : Fin nodeCount -> CNode regionCount
  wires : Fin wireCount -> CWire regionCount nodeCount

structure OpenConcreteDiagram where
  diagram : ConcreteDiagram
  boundary : List (Fin diagram.wireCount)
```

- [ ] **Step 2: Define bounded parent traversal and enclosure**

Define `CRegion.parent?`, then `ConcreteDiagram.climb : Nat -> Fin d.regionCount -> Option (Fin d.regionCount)` with zero steps returning the starting region and a successor following exactly one non-sheet parent. Define:

```lean
def ConcreteDiagram.Encloses (d : ConcreteDiagram)
    (ancestor descendant : Fin d.regionCount) : Prop :=
  exists steps : Fin (d.regionCount + 1),
    d.climb steps descendant = some ancestor

def ConcreteDiagram.ReachesRoot (d : ConcreteDiagram)
    (region : Fin d.regionCount) : Prop :=
  d.Encloses d.root region
```

Prove reflexivity of `Encloses` and synthesize its `Decidable` instance from the bounded `Fin` witness. Do not define an unbounded recursive parent walk.

- [ ] **Step 3: Define node ownership, binder arity, and required ports**

Expose `CNode.region`, `ConcreteDiagram.binderArity?`, and:

```lean
def ConcreteDiagram.RequiresPort (d : ConcreteDiagram)
    (node : Fin d.nodeCount) (port : CPort) : Prop :=
  match d.nodes node with
  | .term _ freePorts _ =>
      port = .output \/ exists i : Fin freePorts, port = .free i
  | .atom _ binder =>
      match d.regions binder with
      | .bubble _ arity => exists i : Fin arity, port = .arg i
      | _ => False
  | .named _ _ arity => exists i : Fin arity, port = .arg i
```

Define `EndpointOccurs d wire endpoint` by list membership and prove or synthesize decidability for `RequiresPort`, `EndpointOccurs`, and the finite universal/existential combinations used by well-formedness.

- [ ] **Step 4: State and prove small ownership facts**

Add named theorems showing `climb 0`, `Encloses.refl`, and the exact required-port shapes for term, valid atom, and named nodes. These are theorem-owned examples, not a separate test file.

- [ ] **Step 5: Elaborate the module**

Run: `lake build VisualProof.Diagram.Concrete.Core`

Expected: the module elaborates without `sorry`, `admit`, or custom axioms.

- [ ] **Step 6: Commit**

```bash
git add VisualProof.lean VisualProof/Diagram/Concrete.lean VisualProof/Diagram/Concrete/Core.lean
git commit -m "feat(formal): define total finite concrete graphs"
```

---

### Task 2: Sole well-formedness contract and exact checker

**Files:**
- Create: `VisualProof/Diagram/Concrete/WellFormed.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Interfaces:**
- Consumes: every predicate from Task 1.
- Produces: the named invariant predicates, `ConcreteDiagram.WellFormed`, `CheckedDiagram`, `OpenConcreteDiagram.WellFormed`, `WFError`, `checkWellFormed`, `checkWellFormed_preserves_input`, `checkWellFormed_complete`, and `checkWellFormed_iff`.

- [ ] **Step 1: State each independently decidable invariant**

Define these named propositions, each with a `Decidable` instance:

```lean
RootIsSheet d
OnlyRootIsSheet d
AllRegionsReachRoot d
AtomBindersAreBubbles d
AtomBindersEnclose d
NamedReferencesResolve signature d
EndpointsAreValid d
EndpointsAreNodup d
WireEndpointsAreDisjoint d
RequiredPortsAreCovered d
WireScopesEnclose d
```

`NamedReferencesResolve` requires `signature[definition]? = some arity` for every named node. `EndpointsAreNodup` is per-wire `List.Nodup`; `WireEndpointsAreDisjoint` forbids one endpoint value appearing in distinct wires; together with `RequiredPortsAreCovered` and `EndpointsAreValid`, these state exact incidence. Where Lean cannot synthesize a dependent finite `Decidable` instance, implement its constructive `Fin` eliminator explicitly rather than adding a Boolean mirror.

- [ ] **Step 2: Assemble the sole contract**

```lean
structure ConcreteDiagram.WellFormed
    (d : ConcreteDiagram) (signature : List Nat) : Prop where
  root_is_sheet : RootIsSheet d
  only_root_is_sheet : OnlyRootIsSheet d
  all_regions_reach_root : AllRegionsReachRoot d
  atom_binders_are_bubbles : AtomBindersAreBubbles d
  atom_binders_enclose : AtomBindersEnclose d
  named_references_resolve : NamedReferencesResolve signature d
  endpoints_are_valid : EndpointsAreValid d
  endpoints_are_nodup : EndpointsAreNodup d
  wire_endpoints_are_disjoint : WireEndpointsAreDisjoint d
  required_ports_are_covered : RequiredPortsAreCovered d
  wire_scopes_enclose : WireScopesEnclose d

abbrev CheckedDiagram (signature : List Nat) :=
  { d : ConcreteDiagram // d.WellFormed signature }
```

Define `OpenConcreteDiagram.WellFormed` as graph well-formedness plus root scope for every ordered boundary incidence. Repetition in `boundary` is intentionally allowed.

- [ ] **Step 3: Declare structured error ownership**

```lean
inductive WFError
  | rootNotSheet
  | secondSheet
  | parentDoesNotReachRoot
  | binderNotBubble
  | binderDoesNotEnclose
  | namedReferenceDoesNotResolve
  | invalidEndpoint
  | duplicateEndpoint
  | endpointOnTwoWires
  | missingRequiredPort
  | wireScopeDoesNotEnclose
  deriving DecidableEq
```

Each constructor corresponds one-to-one with one failed invariant. Do not add a generic `invalid` case.

- [ ] **Step 4: Implement the single checker**

Implement:

```lean
def checkWellFormed (signature : List Nat) (d : ConcreteDiagram) :
    Except WFError (CheckedDiagram signature)
```

as one ordered chain of dependent `if h : Invariant ...` checks. Return the matching error at the first failure and return `⟨d, WellFormed.mk ...⟩` only after all eleven proofs are in scope. Do not introduce `PLift`, a proof box, a custom dependent result, or another checked subtype.

- [ ] **Step 5: Prove exact acceptance**

State first, then prove without admissions:

```lean
theorem checkWellFormed_preserves_input
    (hcheck : checkWellFormed signature d = .ok checked) :
    checked.val = d

theorem checkWellFormed_complete
    (h : d.WellFormed signature) :
    checkWellFormed signature d = .ok ⟨d, h⟩

theorem checkWellFormed_iff :
    (exists checked, checkWellFormed signature d = .ok checked /\
      checked.val = d) <->
      d.WellFormed signature
```

The preservation proof unfolds only the successful checker path. The completeness proof unfolds the checker and discharges every branch from the corresponding field of `h`; proof irrelevance closes the returned subtype equality.

- [ ] **Step 6: Elaborate and scan**

Run: `lake build VisualProof.Diagram.Concrete.WellFormed`

Expected: focused elaboration passes. Scan the concrete modules for `sorry`, `admit`, project `axiom`, `PLift`, custom proof/result wrappers, `Bool` validators, a second checked subtype, and unbounded parent recursion; expect no findings.

- [ ] **Step 7: Commit**

```bash
git add VisualProof/Diagram/Concrete.lean VisualProof/Diagram/Concrete/WellFormed.lean
git commit -m "feat(formal): decide concrete graph well-formedness"
```

---

### Task 3: Theorem-owned acceptance and rejection matrix

**Files:**
- Create: `VisualProof/Diagram/Concrete/Examples.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Interfaces:**
- Consumes: Task 2 checker and error constructors.
- Produces: named graph values and reduction theorems pinning every accepted and rejected representable state required by the design.

- [ ] **Step 1: Define the valid nested example**

Define a three-region graph `sheet -> bubble(1) -> cut`, with a closed term node and a bound atom in the cut sharing one bubble-scoped wire between the term output and atom argument. State and prove:

```lean
theorem validNested_check :
  exists checked, checkWellFormed [] validNested = .ok checked /\
    checked.val = validNested
```

- [ ] **Step 2: Define every rejected graph and state its checker theorem**

Provide minimal concrete values and exact reduction theorems for:

```lean
secondSheet_check = .error .secondSheet
parentCycle_check = .error .parentDoesNotReachRoot
nonBubbleBinder_check = .error .binderNotBubble
escapingBinder_check = .error .binderDoesNotEnclose
namedArityMismatch_check = .error .namedReferenceDoesNotResolve
invalidPort_check = .error .invalidEndpoint
duplicateEndpoint_check = .error .duplicateEndpoint
crossWireEndpoint_check = .error .endpointOnTwoWires
missingPort_check = .error .missingRequiredPort
nonenclosingScope_check = .error .wireScopeDoesNotEnclose
```

Order each fixture so all earlier invariants hold; the theorem must identify the intended first failure rather than an incidental earlier error.

- [ ] **Step 3: Pin bare-wire and repeated-boundary acceptance**

Define a root-only graph with one empty wire and prove it checks. Wrap it with boundary `[0, 0]`, prove `OpenConcreteDiagram.WellFormed`, and prove the boundary length remains two and both positions expose the same wire.

- [ ] **Step 4: Full validation and review gate**

Run: `lake build`

Expected: all modules elaborate. Run `#print axioms` on `checkWellFormed_iff` and the valid nested theorem; only standard Lean proof foundations may appear. Run forbidden-token, alternate-authority, generated-artifact, and diff scans. Request an independent review against the approved design and foundation v8.

- [ ] **Step 5: Commit**

```bash
git add VisualProof/Diagram/Concrete.lean VisualProof/Diagram/Concrete/Examples.lean
git commit -m "feat(formal): prove concrete graph rejection matrix"
```

After Task 3, write the separate checked-elaboration plan against these exact interfaces. Do not begin subgraph algebra until elaboration, concrete isomorphism preservation, and concrete denotation are independently reviewed.
