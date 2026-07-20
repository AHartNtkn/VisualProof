# Seyric First-Principles Content Reconstruction Design

## Outcome

Reconstruct the production Seyric puzzle collection around worthwhile logical and graphical problems. The final collection must expose every approved isolated distinction and the approved cross-topic interactions, remove canonical and experiential padding, preserve open-ended solutions, and derive its size from the surviving content.

This design governs puzzle content and the data surfaces that own it. It does not change proof physics, player moves, the teacher interface, desktop packaging, or unrelated game presentation.

## Controlling principles

- Puzzle count is always an output. It is never a target, floor, cap, batch size, or preservation constraint.
- Existing IDs, folio positions, roadmap slots, evidence roles, and prior authoring effort have no authority.
- Canonical uniqueness is necessary but insufficient. Two different canonical starts are still redundant when they present the same decisions and no new bounded generalization.
- Problems are open-ended. A validation witness proves that a problem is solvable; it is not an intended, unique, shortest, or mandatory solution.
- Teacher pages may explain interactions directly. They cannot create puzzle value that is absent from the start.
- The mandatory Seyric path is exactly the minimal transitive completion set needed to unlock the first Myratic puzzle; every other Seyric record is practice.
- A further example is warranted only when it defeats a plausible narrower interpretation left by the earlier examples. Once the broader pattern is established, larger instances are padding.
- A mixed problem is warranted only when one concept changes another concept's legality, dependency, scope, source or target choice, matching, or consequences. Co-occurrence and independent sequencing are insufficient.
- One record may carry several compatible obligations. The final collection does not allocate a standalone record and a mixed record for equivalent exposure.

## Authoritative content ownership

The runtime and build-time layers remain strict JSON, but the curriculum-shaped authority is removed.

### Core puzzles

`content/puzzles/<puzzle-id>.json` owns only the stable puzzle ID and starting diagram. Backward play and blank completion remain engine invariants.

### Progression

`content/progression/core.json` owns culture order, folio order, explicit puzzle prerequisites, gateways, and culture-unlock conditions. It does not own performances, mastery roles, remediation roles, instructional claims, or a separate required-or-optional classification.

The mandatory Seyric path is derived solely as the minimal transitive set of Seyric completions needed to unlock the first Myratic puzzle. Every other Seyric record is practice. Introduction, retrieval, assessment, challenge, transfer, remediation, and similar labels cannot alter that graph.

### Coverage

`content/coverage/seyric.json` is build-time authoring and audit data. It owns:

- the approved isolated and interaction obligations;
- the visible distinction and saturation rule for each obligation;
- each puzzle's claimed obligations;
- the puzzle's concise visible-situation rationale;
- the narrower interpretation or simpler strategy it defeats;
- the experiential neighbors against which it must be compared.

Coverage data never enters puzzle identity, unlocking, teacher acknowledgment, or runtime behavior. It cannot generate records.

### Catalog

`content/catalog/cursebreaker.json` continues to own culture and artifact names and concise finished provenance. Catalog prose cannot justify retaining a redundant puzzle.

### Guidance

`content/guidance/cursebreaker.json` continues to own optional opening pages, completion commentary, and exact recognized-unwinnable commentary. Guidance references puzzle and intervention IDs only; it no longer references curriculum performance IDs.

### Validation evidence

`content/validation/<puzzle-id>.json` continues to own one complete backward witness, available completed artifacts, the observed witness rule set, and recognized-state demonstrations. Expected rules describe the stored witness and are not acceptance requirements for other solutions.

### Manifest and loading

`content/manifest.json` advances to a new strict version naming puzzles, definitions, progression, coverage, catalog, and guidance. Runtime loading imports the runtime layers and ignores the build-only coverage payload after validating the manifest shape. Content validation loads all layers, including coverage and validation sidecars.

The obsolete curriculum schema, runtime performance types and accessors, learning-role placement arrays, and performance references in guidance are deleted. There is no adapter or compatibility path.

## Additive onboarding augmentation

The accepted practice collection remains intact. Five deliberately simple records precede it so the player can exercise the graphical proof operations before reading a content-bearing propositional seal:

```text
two-veils
├── four-veils (practice)
└── forked-veil
    └── echoed-veil
        └── empty-ring-release
            └── single-mark-return
                ├── first Myratic unlock
                └── preserved Seyric practice graph
```

The empty starts are substantive onboarding content, not incomplete propositional exercises. They isolate boundary highlighting and selection, double-cut release, negative-field fragment erasure, ancestor-supported deiteration, and the distinction between a polarity-changing veil and an ownership ring. `four-veils` adds open-order repetition but is not in the Myratic prerequisite closure.

Progression remains the only authority for this distinction. The mandatory Seyric closure is `two-veils`, `forked-veil`, `echoed-veil`, `empty-ring-release`, and `single-mark-return`; every other Seyric record is practice. The pre-existing practice roots depend on `single-mark-return`, while all pre-existing nonempty practice relationships remain unchanged.

## Approved isolated coverage

These are analytical obligations, not record slots. A final record may carry several when each is genuinely visible.

| Family | Topic | Warranted sequence and stopping point |
| --- | --- | --- |
| Onboarding | Empty cut topology | One bare paired-veil release, one open-order four-veil repetition, one negative-field fragment erasure, and one ancestor-supported cut-form deiteration. |
| Onboarding | Ownership transition | One empty ring between familiar veils, stopping before content-bearing ownership in `single-mark-return`. |
| Hosted | Selection, highlighting, deselection | Explain on `two-veils`, whose bare double-cut release supplies the proof problem; no controls-only record. |
| Hosted | Timeline rewind and branch replacement | Explain on `forked-veil`, whose sibling erasure supplies a real branching problem; no timeline-only record. |
| Primitive | Ownership and vacuity | Single-owner/vacuous elimination; nested-owner discrimination; useful vacuous introduction. |
| Primitive | Polarity | Shallow opposite-polarity contrast; nested parity where rings and cuts defeat local-depth guessing. |
| Primitive | Double-cut elimination | Direct content preservation; compound eligible pair versus obstructed annulus. |
| Primitive | Double-cut introduction | Atomic exact-selection wrap; compound exact-selection wrap. |
| Primitive | Erasure | Atomic complete-fragment erasure; compound semantic-subgraph erasure. |
| Primitive | Insertion | Atomic construction/placement; compound construction as one unit. |
| Primitive | Iteration | Same-region copy; ancestor-to-descendant copy using compound content. |
| Primitive | Deiteration | Exact peer duplicate; ancestor-supported descendant; compound exact-versus-near match. |
| Structural | Weakening | Atomic retained proposition; compound retained proposition through irrelevant context. |
| Structural | Projection | Binary atomic projection; compound conjunct projection; ternary target selection. |
| Structural | Injection | Binary atomic injection; grouped proposition as one branch; ternary alternative-family placement. |
| Structural | Idempotence | Atomic and compound repeated-whole recognition for conjunction and disjunction. |
| Structural | Exchange | Atomic and compound owner-preserving recognition for conjunction and disjunction. |
| Structural | Reassociation | For each connective: minimal three-role recognition, one compound role, and one multiple-site or scope-boundary choice. |
| Constructive | Implication composition | Atomic two-link bridge; compound middle/bridge discrimination; first three-link chain. |
| Constructive | Side-condition composition | Atomic required invariant; compound invariant carried through the connected path. |
| Constructive | Conjunction lifting | Atomic paired transformation; compound paired transformation with correspondence preserved. |
| Constructive | Case analysis | Binary common result; first ternary case with grouped result and genuine common-result discrimination. |
| Constructive | Disjunction mapping | One-branch atomic map; compound two-branch correspondence; first ternary branchwise generalization. |
| Constructive | Distribution and factoring | Four base directional forms; one compound common-conjunction factor; one compound common-disjunction factor. |
| Constructive | Absorption | Atomic and compound repeated-whole recognition for conjunction and disjunction absorption. |
| Classical | Contraposition | Atomic endpoints; one compound endpoint negated and reversed as a whole. |
| Classical | Excluded middle | Atomic, two-variable compound, and three-variable compound forms; stop before a fourth variable. |
| Classical | De Morgan | Four base directions; one compound conjunction-family case; one compound disjunction-family case; one ternary family generalizer. |
| Classical | Reductio | Direct atomic contradiction; compound desired conclusion; assumption-relevant contradiction selection. |
| Classical | Peirce feedback | Atomic feedback proposition; compound repeated feedback proposition. |
| Artifact | Exact theorem selection | Simple exact/near source choice; compound theorem-side exactness. |
| Artifact | Manifestation | One useful legal-target choice; theorem-side complexity is opaque after selection. |
| Artifact | Dissolution | Simple exact occurrence; compound/context-sensitive exact-versus-near occurrence. |

Content double negation receives no independent records beyond the double-cut sequence. Structural transfer, practice, challenge, remediation, retrieval, and assessment are not content topics. Fusion is excluded because pure-propositional Seyric diagrams have no wires.

## Approved cross-topic coverage

### Interactions carried by isolated records

The final shapes for these isolated obligations must also expose the interaction, without creating another record solely for the combination:

| Interaction | Required visible distinction |
| --- | --- |
| Hosted scope, ownership, polarity, and local edit legality | Similar targets whose actual semantic host changes whether insertion, erasure, or weakening is legal. |
| Annulus ownership and double-cut eligibility | An eligible pair and an obstructed near-match whose blocker actually belongs to the annulus. |
| Ancestry-sensitive iteration/deiteration | Equal-looking occurrences in ancestor, descendant, and sibling relations with different authority. |
| Structural recognition guiding routing | Exchange or reassociation recognition determines the component projected or alternative constructed, without inventing a structural rewrite. |

### Distinct mixed families

| Family | Minimum worthwhile shape | Saturation |
| --- | --- | --- |
| Boundary topology changes copy authority | A double-cut topology change creates or removes the ancestry relation needed by iteration/deiteration. | One copy-license mutation. |
| Temporary double-cut workspace | A double cut creates an opposite-polarity annulus in which a useful edit becomes legal. | One insertion-oriented and one erasure-oriented workspace. |
| Simplification threatens a future source | A removable occurrence or side condition is also the sole source for a later structural or logical dependency. | One structural-source case and, only if diagrammatically distinct, one implication-bridge case. |
| Product-to-sum handoff | A relation analogous to `(A ∧ B) → (B ∨ C)`. | One grouped handoff; larger arity is already covered in isolation. |
| Extraction feeds a continuation | A product result contains the exact component consumed by a later implication. | One product and one continuation. |
| Context-threaded serial composition | A changing proposition crosses a chain while a side condition must survive to a later consumer. | One preserved context and the first distinct required/irrelevant-context case. |
| Branch preparation and convergence | A common-tail topology and a branch-local-chain topology. | One of each; additional branches or hops are padding. |
| Shared context across a branch boundary | Shared context is exposed for branch-local consumers or recollected after branch mapping. | One expose and one recollect topology. |
| Shape change exposes hidden redundancy | Factoring or distribution reveals an absorption or idempotence redex. | One conjunction-field and one disjunction-field topology. |
| Negation creates the next consumer topology | De Morgan produces a product for projection/lifting or alternatives for mapping/case analysis. | One product-producing and one sum-producing problem. |
| First alternating negation/normal-form interaction | One alternating connective boundary requires both De Morgan and distribution. | One CNF-shaped and one DNF-shaped topology. |
| Contrapositive bridge | Contraposition changes an otherwise unusable implication into the missing composition bridge. | One reversed bridge. |
| Excluded middle manufactures cases | No split is supplied; the two downstream handlers identify the useful excluded-middle proposition. | One split; compound structure only when branches consume it. |
| Structured contradiction under reductio | A compound consequence conflicts with separately available negated components under the reductio assumption. | One compound contradiction with a meaningful competing source. |
| Classical consensus across a factor boundary | The branch-building and product-collapsing dual relations combine factoring/distribution with excluded middle. | One of each dual topology. |
| Artifact direction selected by polarity | One completed record has a possible exact dissolution site and an absent manifestation field at different polarities. | One nested-parity contrast. |
| Artifact supplies a downstream bridge | The useful completed record is determined by a later chain or branch dependency. | One bridge; retain a second only if linear and branching diagrams create different choices. |
| Artifact content creates or destroys structural authority | Ordinary manifested content creates an ancestor source, or dissolution would remove that source. | One source-creation and one source-preservation topology. |

Peirce receives no mixed family unless a concrete closed formula later demonstrates a changed feedback dependency rather than compound Peirce followed by ordinary setup. Exchange and reassociation never act as local normalization moves. Manifested artifacts never retain special provenance.

## Reconstruction procedure

### 1. Freeze the obligation model

Encode the approved isolated and interaction obligations in coverage data before deciding which current IDs survive. Each obligation records its distinction and stopping rule. No current record may create a new obligation by existing.

### 2. Audit the current collection

For every current Seyric puzzle:

1. compute its canonical starting fingerprint;
2. group exact duplicates;
3. group experiential neighbors by logical family, dependency topology, operand complexity, and graphical scope;
4. determine which approved obligations are visibly present;
5. reject records justified only by role labels, formula renaming, larger saturated arity, longer saturated chains, mirrored positions, or catalog prose;
6. retain the clearest feasible representative when several starts provide equivalent exposure.

The audit is content judgment supported by automatic evidence. Automatic validity, witness replay, or canonical inequality never establishes value by itself.

### 3. Construct missing starts

Author concrete closed Seyric diagrams only for uncovered approved obligations. Start with the smallest topology that makes the distinction legible. Add the first compound, ternary, dual, or mixed form only where the approved stopping rule warrants it.

Authors may explore alternative witnesses freely. They must not add decoys to force a route, reject shortcuts, or create another record when an existing mixed start already provides the same exposure.

### 4. Order the resulting collection

Order records by the minimum concepts needed to read them, then place mixed records after their participating concepts have appeared. This ordering supports comprehension but is not a mastery curriculum.

Practice records may depend on completed source artifacts and may sequence other practice records. They remain outside the mandatory Seyric path unless their completion is in the transitive graph that unlocks the first Myratic puzzle. No conceptual or pedagogical label can change that definition.

### 5. Finish every content layer

Every retained or newly authored record receives exactly one core diagram, progression placement, artifact entry, coverage mapping, validation sidecar, and optional guidance entry. Deleted records are removed from every layer, static import, test fixture, and documentation reference. No alias, tombstone, compatibility map, or fallback preserves them.

## Parallel authoring and review

After the current audit identifies independent obligation families, authors work in disjoint scratch directories and return complete bundles. They do not edit shared production registries.

The lead integrates accepted bundles and owns all shared ordering and registration files. Each batch receives two independent reviews:

- a logical/content review checks closedness, witness replay, exact artifact authority, concept accuracy, and feasibility;
- an adversarial coverage review checks the claimed visible distinction, experiential neighbors, saturation, open-endedness, and whether every mandatory-path edge is genuinely necessary to unlock the first Myratic puzzle.

A single concrete defect overrides vague approvals. Reviews do not reject alternative solutions.

## Validation

### Direct content checks

- every runtime JSON layer decodes strictly;
- every puzzle has exactly one progression placement, catalog record, coverage mapping, and validation sidecar;
- every witness replays backward to canonical blank;
- every recognized-state demonstration reaches its declared state;
- every artifact dependency is available from actual prerequisites;
- the mandatory Seyric path equals the transitive prerequisite closure of the first Myratic unlock condition;
- every claimed obligation exists and every approved obligation has coverage;
- no puzzle claims value solely through teacher text or witness rule names.

### Redundancy checks

- no duplicate canonical starting fingerprint;
- explicit experiential-neighbor groups have one rationale per surviving distinction;
- no saturated variable, branch, chain, nesting, or dual ladder survives without a recorded false hypothesis;
- coverage review lists deleted neighbors and the reason they add no experience;
- alternative valid solutions remain accepted.

### Displaced-model checks

Repository searches and type tests must prove the absence of:

- the obsolete numeric inventory authority;
- slot-preservation or inventory-preservation policy;
- runtime curriculum performances and learning-role arrays;
- role-generated introduction, practice, retrieval, assessment, remediation, challenge, or transfer records;
- the obsolete roadmap, normalization receipt, and parallel quota-shaped authoring plan;
- stale IDs in manifests, imports, catalog, guidance, progression, coverage, validation, tests, or docs;
- exchange/reassociation transformation claims or persistent artifact-provenance claims.

### Execution checks

Run focused content tests, content validation, TypeScript checking, and the renderer build. Run browser validation only for archive ordering, unlock behavior, guidance availability, and artifact dependencies affected by the final collection. Do not run the unchanged dedicated physics battery or launch the fullscreen desktop application.

## Completion evidence

Completion requires an itemized final receipt containing:

- every approved isolated and interaction obligation with its covering puzzle or explicit fixed-semantics rejection;
- every retained puzzle with its visible-situation rationale and experiential-neighbor comparison;
- every deleted puzzle with the non-value reason and proof that no dependent reference remains;
- every newly authored puzzle with witness replay and both independent reviews;
- the derived mandatory Seyric path and the exact graph edge justifying every member;
- validation command outputs and zero-count defect checks.

The refactor is not complete while any retained record lacks a complete bundle, any approved obligation lacks coverage, any redundant required-or-optional declaration remains, or any obsolete inventory authority remains.
