# Inconsistent Cut Elimination Design

## Outcome

VisualProof gains a native proof step named `inconsistentCutElim`. It removes a cut when two distinct closed term nodes directly inside that cut share an output wire and carry finite, mechanically replayable reduction paths to syntactically distinct beta-eta normal forms.

The rule is a polarity-independent equivalence. Backspace and Delete discover and apply it through the existing contextual deletion interaction in forward and backward proving. TypeScript and Lean expose one matching 26-form proof language, and Lean proves the executable concrete transformation sound against canonical elaborated semantics.

## Logical Boundary

The trusted fact is finite normal separation, not a general disequality oracle. A certificate contains only two explicit reduction paths:

```ts
export type NormalSeparationCertificate = {
  readonly firstSteps: readonly ReductionStep[]
  readonly secondSteps: readonly ReductionStep[]
}
```

Replay applies each path to its corresponding source term. It then checks that neither endpoint admits a beta or eta reduction and that the endpoints are syntactically unequal. Church-Rosser and uniqueness of beta-eta normal forms justify non-convertibility. Because both source terms denote the individual carried by their shared output wire, their equations contradict each other. Extra conjuncts in the cut body cannot restore satisfiability, so the cut denotes true and may be removed from its parent conjunction in either orientation and at any depth.

The production implementation and formalization do not recognize constants, encodings, named terms, head forms, or special syntax beyond generic lambda-term reduction.

## TypeScript Certificate and Replay Gate

The term layer owns `NormalSeparationCertificate` and a fuel-free checker alongside the existing reduction certificate machinery. The checker:

1. starts from each source term;
2. applies the stored `ReductionStep` values in order with `applyStepAt`;
3. reports the side and step index for an invalid path;
4. checks both resulting terms with the existing beta and eta one-step operations;
5. rejects either reducible endpoint;
6. rejects syntactically equal endpoints using `termEq`; and
7. returns both checked normal endpoints only on success.

The checker never calls `normalize`, accepts empty paths for already-normal terms, and has no fuel input.

The kernel rule lives under `src/kernel/rules/` and accepts a diagram, cut region ID, two node IDs, and the certificate. Its gate checks, in order:

- the region exists and is a cut;
- both node IDs exist, denote term nodes, and are distinct;
- both nodes have the cut as their immediate `region`;
- both nodes have empty authoritative `freePorts` interfaces;
- their output endpoints resolve to the same wire;
- the normal-separation certificate passes the fuel-free checker.

On success, the rule constructs the canonical selection whose anchor is the cut's parent and whose only child root is the cut. It passes that selection to `removeSubgraph`. That existing operation remains the sole deletion authority: it removes the entire region subtree, all subtree-owned nodes and wires, and trims removed endpoints from surviving wires before `mkDiagram` revalidates the result.

The rule has no orientation parameter because its semantics are equivalence in every polarity.

## Authoring Search

Authoring discovery is separate from replay. Given a selected cut and the shared UI fuel, it:

1. collects only term nodes whose immediate region is the cut;
2. sorts node IDs using the repository's canonical lexical convention;
3. enumerates unordered distinct pairs in that stable order;
4. filters to pairs with empty free-port interfaces and one shared output wire;
5. normalizes the first and second terms independently with `normalize` and the same fuel;
6. records fuel exhaustion but continues to later pairs;
7. skips pairs whose completed normal forms are syntactically equal; and
8. returns the first stable certifying pair with its two normalization paths.

Discovery has three outcomes:

- `certified`: return node IDs and the certificate;
- `undecided`: no pair certified, but at least one structurally plausible pair exhausted fuel;
- `absent`: no pair certified and none exhausted fuel.

`undecided` produces a refusal explaining that inconsistency is undecided under the current fuel. It does not fall through to ordinary erasure because doing so would hide a potentially available equivalence behind a polarity-dependent rule. `absent` continues to the next contextual deletion meaning. The kernel rechecks every emitted certificate and trusts none of the discovery conclusions.

## Proof Language Integration

`ProofStep` gains exactly this constructor:

```ts
{
  readonly rule: 'inconsistentCutElim'
  readonly region: RegionId
  readonly first: NodeId
  readonly second: NodeId
  readonly certificate: NormalSeparationCertificate
}
```

`applyStep` dispatches it directly to the kernel rule in both orientations. The normal endpoints and authoring fuel are not serialized.

Strict JSON uses one certificate object with exactly `firstSteps` and `secondSteps`. Each step uses the existing strict reduction-step shape. Parsing rejects missing IDs, missing certificate arrays, unknown fields at either level, malformed path segments, invalid reduction kinds, and incorrectly typed values. No alias tag or alternate certificate spelling is accepted.

Composition remaps `region`, `first`, and `second` through the meet isomorphism while leaving reduction paths unchanged. Action replay, theorem checking, forward and backward sessions, and boundary receipts use the existing exhaustive proof-step machinery. The removal receipt naturally preserves surviving root wires by identity and reports removed wires as absent through the current root-filtered transport.

All rule exports and exhaustive switches gain the new constructor. The TypeScript union remains the source inspected by the generated Lean/TypeScript tag checker.

## Contextual Deletion and Menus

Proof-action discovery adds an `inconsistentCutElim` descriptor for a single absorb-normalized selected cut with at least one structurally plausible direct closed shared-output pair. The descriptor is polarity-blind.

The contextual deletion resolver uses this priority:

1. double-cut elimination;
2. vacuous-bubble elimination;
3. inconsistent-cut elimination;
4. ordinary erasure;
5. deiteration.

For the inconsistent-cut position, the resolver runs authoring discovery with the current shared fuel. `certified` emits the native proof step, `undecided` raises the dedicated refusal, and `absent` continues to erasure or deiteration.

`ProofMoveController` already sends both Backspace and Delete through one branch and obtains orientation and fuel from shared options. That branch remains the only keyboard path. Context menus use the same certificate-authoring function when the inconsistent-cut action is chosen. No shortcut, mode, controller, dialog, or confirmation is added.

`discoverProofActions` continues to build selections from `absorbHits`. Therefore selecting the cut alone or selecting the cut together with nodes, wires, and descendant regions yields the same canonical cut selection and the same contextual result.

## Lean Lambda Certificate

Lean adds an executable beta-eta normality predicate because the current formalization defines only the proposition:

```lean
def Normal (term : Term n α) : Prop :=
  ∀ next, ¬ OneStep term next
```

The executable checker recursively detects root beta/eta redexes and redexes beneath lambda bodies and application children. Its principal correctness theorem states that a successful check is equivalent to `Normal`; supporting lemmas connect detected redexes with `OneStep` and show every `OneStep` is detected. No normalization function or normalization axiom is introduced.

Lean's `NormalSeparationCertificate first second` contains the two raw reduction paths plus the proof-bearing result of executable checking: `checkPath` reaches `firstNormal` and `secondNormal`, both normality checks succeed, and the endpoints are unequal. Its public theorems provide:

- `Reduces first firstNormal` and `Reduces second secondNormal` from checked paths;
- `Normal firstNormal` and `Normal secondNormal` from normality-check correctness;
- `¬ BetaEta first second` via `not_betaEta_of_normal_ne`; and
- `quote first ≠ quote second` via `quote_eq_iff`.

The generic local contradiction theorem is:

```lean
theorem shared_output_closed_terms_false
    (certificate : NormalSeparationCertificate first second) :
    ¬ ∃ output : Individual,
      output = quote first ∧ output = quote second
```

It quantifies over arbitrary closed terms and uses no named examples or additional axioms.

## Lean Executable Rule

The proof-bearing Lean payload refines the serialized identifiers against the current checked diagram. It records:

- a cut region and its parent;
- two distinct node indices;
- equations showing both are zero-free-port term nodes directly in the cut;
- one wire with occurrences of both output endpoints;
- the raw normal-separation certificate and its successful executable check; and
- the canonical checked selection anchored at the parent with exactly the cut as its child root and no direct nodes or explicit wires.

The new `Step` constructor carries the region, node indices, and payload. `Step.tag`, `StepTag.all`, serialized names, semantic classification, error vocabulary, and all exhaustive cases gain `inconsistentCutElim`. It is classified as `equivalent`.

The executable applier checks the payload's certificate result, performs the established `ConcreteDiagram.removeRaw` transformation on the canonical cut selection, checks well-formedness through the existing removal theorem, and returns the standard removal provenance and interface transport. It does not call normalization and has no orientation-sensitive branch.

## Lean Semantic Soundness

The soundness development connects the concrete gate to actual elaborated cut semantics rather than stopping at a proposition-level contradiction.

First, compiler-facing lemmas identify the two direct zero-port term nodes as equation items in the selected cut body and identify their common output wire value. `shared_output_closed_terms_false` makes the conjunction of those two equation items false. Existing item-sequence conjunction lemmas show that arbitrary other nodes, wires, and child regions cannot make the cut body true.

Second, the existing cut denotation equation turns the false body into a true cut item. Item-sequence append/permutation lemmas show that removing this true item preserves the parent conjunction.

Third, the concrete removal decomposition and canonical reassembly semantics connect that local equivalence to the actual `removeRaw` result. Existing context/splice congruence transports it through every ancestor region, including nested cuts and bubbles. The resulting receipt-level theorem proves `SuccessfulReceiptSound` for every transported ordered boundary. Because the tag is equivalent, the theorem supplies both directions independently of proof orientation.

`applyStep_sound`, open replay soundness, theorem soundness, and theory soundness then inherit the new case through their existing exhaustive dispatchers. Public imports expose the rule and the audit prints the new principal certificate and rule soundness theorems.

## Correspondence Inventory

`StepTag` and `StepTag.all` gain `inconsistentCutElim` in the same serialized order as the TypeScript union. Length theorems change from 25 to 26. `serializedName` maps the constructor to exactly `"inconsistentCutElim"`; injectivity and exact-membership proofs remain exhaustive.

The repository's `scripts/check-lean-step-tags.mjs` remains the sole correspondence generator/checker. No generated output is hand-authored.

## Testing Strategy

Focused TypeScript tests cover the kernel gate, authoring search, contextual interaction, structure, persistence, and remapping.

Kernel tests establish empty certificates for already-normal distinct closed terms, nonempty replayable paths for reducible terms, successful removal with arbitrary additional cut content, trimming of ancestor-scoped shared wires, removal of cut-scoped wires, preservation of unrelated IDs and objects, and polarity/orientation independence. Negative cases cover open terms, descendant nodes, different output wires, equal normal forms, invalid paths, reducible certificate endpoints, missing entities, and repeated node IDs.

Authoring and interaction tests establish stable candidate choice, continuation after equal and exhausted pairs, the dedicated final undecided outcome, no emitted step on exhaustion, replay independence from later UI fuel changes, Backspace/Delete identity, absorb-normalized selections, priority over erasure, forward/backward parity, and contextual menu availability.

JSON tests cover exact round trips plus missing, unknown, and mistyped certificate fields and malformed reduction steps. Composition tests verify remapping of all three host IDs while preserving the certificate.

Lean examples use arbitrary constructors to exhibit one already-normal distinct pair and one reducible pair reaching distinct normal forms. They exercise the executable certificate and rule boundary without giving any term privileged production behavior.

## Validation

Focused tests and Lean modules run during implementation. Completion requires green results from:

```text
npm test
npm run typecheck
npm run formal:tags
lake build
rg -n 'sorry|admit|decreasing_by sorry|^axiom ' VisualProof
git diff --check
```

The source audit must find no prohibited proof placeholders or project-defined axioms. The tag checker must report exactly 26 matching tags. Validation failures caused by the implementation are repaired and rerun; only an external constraint may remain as a reported blocker.
