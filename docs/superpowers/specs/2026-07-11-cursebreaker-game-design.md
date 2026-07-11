---
name: cursebreaker-game-design
created: 2026-07-11
status: draft-for-user-review
---

# Cursebreaker — Game Design Specification

## 1. Product outcome

Cursebreaker is a self-contained abstract puzzle game built from the visual proof engine. The player examines magical artifacts through a brass lens and breaks their seals by transforming each diagram backward until only the blank sheet remains.

The game is the sole product on its branch. The proof-assistant application remains on `main`; the game branch contains no sibling assistant, hidden assistant mode, feature flag, compatibility shell, theory editor, arbitrary theorem authoring, filesystem library, import, export, or save-theory path.

These are catalog and product-surface constraints, not demands to narrow the reusable proof engine. The underlying kernel may retain general theorem, boundary, and proof capabilities when the bundled game content and player interface do not expose them.

The proof assistant on `main` is the sole owner of proof interactions. The game may
decorate those interactions but must not define a proof gesture or command that is
absent from the assistant. A missing interaction is implemented and validated on
`main` first, then brought into the game through branch integration.

The intended player enjoys abstract puzzle games and may know no formal logic. The game must be enjoyable and learnable without referring to propositions, quantifiers, inference, lambda calculus, or its mathematical origin. Exact formal statements remain authoritative content metadata and validation evidence, not required player-facing language.

## 2. Non-negotiable game model

Every puzzle is one closed, zero-boundary theorem. Its implicit source is always the unique blank sheet; arbitrary left- and right-hand theorem sides are not representable in the game catalog.

Play is exclusively backward. A puzzle begins at its theorem diagram and ends automatically when the current diagram is canonically equal to blank. There is no forward proof, second proof front, meet-in-the-middle mode, declaration action, theorem adoption, or direction control.

Each accepted move produces a new immutable diagram state. The kernel remains the sole authority for move legality. A refused move changes neither the diagram nor the timeline.

First completion is durable. Rewinding a completed puzzle does not revoke its completion, prerequisites, or solved-seal vellum.

## 3. Timeline interaction

The existing single-track timeline semantics remain unchanged and become a brass lever assembly along the bottom of the main lens.

- Every notch represents one exact retained diagram state.
- The lever position is the authoritative cursor.
- The diagram under the lens is always the cursor state.
- The player can scrub freely backward and forward.
- Rewinding retains future states.
- Applying a move from an earlier state truncates the abandoned future and appends the new continuation.
- Hover or keyboard focus may preview the adjacent transition, but preview is never a second history authority.

Past, current, and future notches must be distinguishable without relying on color alone. Timeline branching is a safe experimentation affordance, not a logical skill whose use is required merely for assessment.

## 4. Solved-seal vellums

Completing a puzzle records its identity, unlocks dependent artifacts, and adds the exact closed theorem to the vellum library.

A vellum exposes exactly two inverse actions:

1. Manifest one complete copy of its closed seal inside a chosen region.
2. Dissolve one exact canonical occurrence of that complete seal.

Vellums have no boundary arguments, partial matches, alternate sides, arbitrary replacement, direction choice, or compatibility with the proof assistant's general theorem application. A later puzzle may manifest an outer-quantified seal and then specialize it through ordinary game mechanics; this does not turn the vellum itself into a parameterized rewrite rule.

Authoring validation must detect accidental one-move solutions in which a later goal is merely the obvious whole occurrence of a newly unlocked vellum.

## 5. Desk presentation

The game presents one orderly working curator's desk with slight physical asymmetry.

### 5.1 Main lens

- A rounded-square brass lens dominates the center and fills nearly the full viewport height.
- The active artifact diagram remains crisp and visually primary beneath the glass.
- The left folio owns culture and artifact navigation.
- The right-side vellums own solved seals and their organization.
- Papers may be slightly skewed, but interaction positions remain predictable.
- At compact widths, side papers collapse into edge stacks or drawers while the main lens remains dominant.

### 5.2 Teacher and feedback

A teacher provides brief dialogue at authored instructional or story beats, then gets out of the way. Instruction explains an affordance or visible constraint, never a complete move sequence.

Invalid actions appear as concise first-person thoughts near the attempted pointer location. Thought bubbles use a subtle red treatment and a non-color cue. Examples of the intended voice include:

- “That mark is held from this side of the veil.”
- “There’s no older twin supporting this copy.”
- “That mark belongs to a different seal.”
- “Those mechanisms don’t turn into the same shape.”

Kernel refusals remain authoritative. The presentation layer translates them into diegetic copy without swallowing, weakening, or converting the failed action into a fallback.

### 5.3 Construction loupe

The existing comprehension construction workflow remains behaviorally authoritative but is presented as a large circular magical loupe.

- The loupe glass is the full independent diagram-construction surface.
- The instrument is large enough for real use and never becomes a miniature magnifier.
- Brass rim and handle sit outside the usable glass.
- Gripping clear rim or handle moves the loupe.
- The established resize interaction is expressed through the physical handle treatment.
- The host artifact remains visible and interactive for existing host/draft connection gestures.
- Connection feedback appears only during the active connection drag; no persistent connector is drawn.
- No dialog rectangle, title bar, menu strip, labels acting as menus, orbiting buttons, or controls inside the glass survive.
- Ctrl+Z and Ctrl+Shift+Z traverse local construction history.
- Enter finalizes the construction.
- Escape or Backspace closes it without committing.
- Construction, selection, connection planning, local history, cancellation, and atomic commit retain their established semantics.

### 5.4 Visual-direction review

Layout mockups establish composition, scale, hierarchy, and interaction geometry only. They are not production visual targets and must not be promoted into the game merely because their formatting was approved.

Before adopting a material aesthetic direction, present a small set of coherent options as representative in-game demos and discuss them with the user. Each demo must show the real interface at realistic content density—including the main lens, artifact diagram, surrounding papers or vellums, and any affected loupe, teacher, or thought treatment—rather than isolated swatches or ornamental fragments. The options should make meaningful differences in materials, lighting, typography, ornament, animation, and atmosphere visible without changing approved interaction semantics.

Production styling begins only after the user selects or refines a demonstrated direction. Acceptance requires a unified, intentionally crafted result that looks appropriate for a polished puzzle game; a functional wireframe, lightly decorated utility interface, or direct rendering of the formatting mockups is insufficient.

## 6. Content and progression authority

One immutable bundled catalog is the only source of game content. Every artifact contains:

- stable artifact identity and culture identity;
- exact closed theorem diagram;
- verified backward solution witness;
- content fingerprint;
- prerequisite artifact and knowledge-node identities;
- mechanics introduced, practiced, retrieved, and assessed;
- required vellum dependencies;
- diegetic title and artifact description;
- teacher beats and optional escalating hints;
- misconception-specific feedback categories.

A build-time verifier rejects:

- nonempty theorem boundaries;
- goals whose witness does not replay backward to canonical blank;
- cyclic, missing, or unreachable prerequisites;
- unavailable or circular vellum dependencies;
- duplicate identities or unstable fingerprints;
- claimed mechanics absent from the verified trace;
- references to proof-assistant-only content or actions.

Progress derives unlocked artifacts and available vellums solely from the catalog plus completed puzzle identities. The versioned local save contains progress, settings, and the active puzzle timeline. It contains no external theory, arbitrary authored diagram, filesystem authority, or imported proof object.

## 7. Mastery-learning content contract

The curriculum is a prerequisite DAG of small observable performances, not a chapter list or theorem-name checklist. Player-visible groupings are the sealing traditions of different cultures, not linear campaigns. Each culture contains a required mastery spine plus elective practice, retrieval, remediation, and challenge artifacts.

The tutorial spans several cultures and continues through approximately the fixed-point theorem. Unlocking a later culture does not close an earlier one or require every artifact in it; only artifacts in the prerequisite closure of later content are progression requirements.

Every retained performance requires:

1. Brief direct instruction.
2. One low-noise isolated use.
3. A contrast with its nearest tempting mistake.
4. At least two structurally varied applications.
5. Delayed retrieval after intervening content.
6. Mixed use with older skills.
7. An unprompted transfer artifact.

After initial proficiency, ordinary content should target approximately 50–60% current-culture skills, 25–35% recent skills, and 10–20% distant retrieval. Culture advancement depends on transfer artifacts rather than raw puzzle count, completion speed, or move count.

Repeated categorized errors may offer one concise teacher observation and unlock an optional contrast/remediation artifact. Returning from remediation preserves the original puzzle timeline.

Every candidate mechanic family must pass a representative feasibility spike before exact artifact counts are committed:

- one closed zero-boundary theorem;
- a legal backward trace through exposed game interactions;
- evidence the advertised mechanic is load-bearing;
- no accidental one-step vellum solution;
- a readable diagram independent of layout accidents.

If a retained kernel mechanic does not create a distinct, intelligible player decision in backward play, it must be removed from the player-facing surface rather than justified through filler puzzles.

## 8. Curriculum roadmap

The roadmap deliberately introduces one new representational ontology at a time: regions and proposition marks; nested proposition binders; individual wires and relations; named relational forms; term anatomy and computation; recursion; then substantial mathematical applications.

Exact artifact lists remain deferred until the prerequisite graph, mechanic matrix, and representative feasibility proofs are validated.

### 8.1 Oldest propositional culture — initial instruction

The oldest surviving sealing tradition is structurally primitive. Its simplicity makes it the opening instructional culture, but it is only the beginning of the tutorial rather than a bounded tutorial of its own.

Must include:

- “Two Veils”: `¬¬⊤`.
- “Four Veils”: `¬¬¬¬⊤`.
- Cut nesting and move legality.
- Insertion/erasure and iteration/deiteration in small proposition seals.
- Timeline scrubbing, retained future, and branch replacement.
- Early outer arity-zero proposition bubbles.
- One low-noise construction-loupe substitution.
- One obvious whole-vellum use after several seals have been solved.

Exit evidence: independently read a small seal, use the timeline, understand atomic refusals, and complete a simple outer-quantified proposition puzzle.

### 8.2 Oldest propositional culture — outer-universal development

This is the substantial continuation of the same pure-propositional culture. Nearly every theorem has outer closure of the form `∀P,Q,R,…`. Non-universal proposition quantification belongs to the next culture.

Required theorem families:

- identity;
- weakening, projection, and injection;
- contraction and idempotence;
- exchange and reassociation;
- implication composition with three or more propositions;
- conjunction and disjunction algebra;
- case analysis;
- distribution and absorption;
- contraposition and De Morgan families;
- delayed classical families: excluded middle, double-negation elimination, reductio, and Peirce-style forms;
- exact vellum choice among multiple older seals;
- the same semantic family in structurally different diagrams.

Exit evidence: solve unfamiliar multi-proposition seals through polarity and structural reasoning without stepwise dialogue or silhouette matching.

### 8.3 Later proposition-binder culture

This remains proposition-only. It begins with non-universal proposition quantification and later develops nested binders. Individual wires and equality are absent.

Required families:

- vacuous proposition quantification;
- independent-binder exchange;
- atomic and compound arity-zero instantiation;
- binders nested inside implication, negation, conjunction, and other binders;
- quantifier movement with explicit non-occurrence conditions;
- valid distribution paired with similar invalid cases;
- shadowed versus independent binder ownership;
- multiple occurrences at different depths;
- impredicative proposition encodings when they produce clear puzzles.

Exit evidence: predict binder ownership, construct compound proposition substitutions, and distinguish scope errors from polarity errors.

### 8.4 First-order identity and relations — no lambdas

This introduces anonymous individuals as scoped wires. Lambda anatomy does not appear, even decoratively.

Required families:

- existential and universal wire scope;
- identity through shared topology;
- wire join and sever under their gates;
- reflexivity, symmetry, and transitivity;
- equality chains;
- substitution into unary and binary relation positions;
- shared versus independent witnesses;
- repeated arguments such as `R(x,x)` versus `R(x,y)`;
- same-kind quantifier exchange;
- alternating quantifiers such as `∀x∃y` versus `∃y∀x`;
- mixed first- and second-order relation schemas.

Fusion/fission, congruence joining, endpoint transport, and head stripping are excluded here because their implemented semantics are term-specific rather than generic first-order equality.

### 8.5 Relational systems and definitions

This may become its own culture or the advanced half of the preceding culture after representative playtests.

Required families:

- arity-one and arity-two comprehension;
- ordered boundary attachments;
- diagonal and repeated attachments;
- open comprehensions referencing enclosing binders;
- transparent named unary and binary relations;
- selective relation fold/unfold;
- relational converse, composition, domain, range, functionality, symmetry, and transitivity;
- later graph-, order-, membership-, or arithmetic-like structures;
- problems where indiscriminate unfolding creates clutter.

Definitions compress already-understood relations. They never conceal an unfamiliar representation.

### 8.6 Lambda grammar and terminating computation

Required progression:

1. Read one binder and one bound use.
2. Read application anatomy and association.
3. Introduce closed term nodes.
4. Recognize producer/consumer structure.
5. Fuse and fission simple subexpressions.
6. Perform one β step.
7. Handle discarded and duplicated arguments.
8. Follow nested β chains.
9. Explore alternative reduction orders with the timeline.
10. Introduce η and its side condition.
11. Prove equality of terminating computations.

Bare goals such as `∃x.x=t` are prohibited because closed-term introduction makes them trivial.

### 8.7 Term equality and combinators

Secondary term-specific mechanics are introduced only after term anatomy and βη conversion:

- congruence join after conversion evidence and co-residence;
- endpoint transport using closed convertible evidence;
- head normalization before head stripping;
- head stripping only for aligned rigid spines with shared outputs.

Every selected combinator receives two linked theorem families:

1. Its operational equation, established from its explicit lambda structure.
2. The relational interpretation of its polymorphic type, using the operational theorem and earlier logical skills.

The recursive interpretation is:

- `[[X]](t) := X(t)` for a unary relation variable;
- `[[A → B]](f) := ∀x. [[A]](x) → [[B]](f x)`;
- `[[∀X.A]](t) := ∀X. [[A]](t)`.

Required combinator families include:

- `I : ∀X. X→X`;
- `K : ∀X,Y. X→Y→X`;
- `B : ∀X,Y,Z. (Y→Z)→(X→Y)→X→Z`;
- `C : ∀X,Y,Z. (X→Y→Z)→Y→X→Z`;
- `W : ∀X,Y. (X→X→Y)→X→Y`;
- `S : ∀X,Y,Z. (X→Y→Z)→(X→Y)→X→Z`.

For example, K's relational theorem is `∀X,Y,x,y. X(x) → Y(y) → X(K x y)`. The player sees the visual seal; the formal type and expansion remain content metadata and test authority.

These are operational/relational preservation properties, not uniqueness or unsupported categorical universal properties.

### 8.8 Fixed-point foundations

Required progression:

- self-application as a local term shape;
- repeating term structures;
- targeted conversion versus global normalization;
- finite common-reduct certificates;
- explicit fixed-point construction;
- closed operational property `∀f. Y f = f(Y f)`;
- if newly derived and playable, the existential consequence `∀f. ∃x. x=f x`.

The game must not assign Y the unsupported relational type `∀X.(X→X)→X`. The operational equation alone does not establish that claim for arbitrary predicates.

### 8.9 Boolean theory — first synthesis culture

Core representations:

- explicit Church true and false terms;
- `Boolean(b) := ∀P. P(true) → P(false) → P(b)`.

Required families:

- `Boolean(true)` and `Boolean(false)`;
- unfolding and refolding `Boolean`;
- Boolean case analysis derived through comprehension;
- operational selector equations for true and false;
- definitions and operational behavior of not, and, or, xor, and conditional selection;
- closure typings such as `Boolean(b) → Boolean(not b)` and `Boolean(a) → Boolean(b) → Boolean(and a b)`;
- identity and annihilator laws;
- idempotence where applicable;
- `not(not b)=b`;
- commutativity and associativity;
- De Morgan laws;
- selected distributive laws.

The culture progresses from operational equations to proofs using Boolean case analysis. Its capstone combines several operational and closure vellums rather than reproducing a truth table.

### 8.10 Natural-number theory — final synthesis culture

Core representations:

- explicit Church zero and successor;
- `Nat(n) := ∀P. P(zero) → (∀m. P(m) → P(succ(m))) → P(n)`.

Required families:

- `Nat(zero)`;
- `Nat(n) → Nat(succ(n))`;
- unfolding and refolding `Nat`;
- unary, nested, and parameterized induction predicates constructed through comprehension;
- explicit Church addition;
- base and successor recursive equations for addition;
- `Nat(m) → Nat(n) → Nat(m+n)`;
- a recursive addition functional Φ;
- a closed existential or pointwise equivalence between ordinary Church addition and the Y-defined operation `Y Φ`;
- left and right unit laws;
- successor shift on the non-recursive argument;
- associativity when required by the selected final proof;
- every equality-transport and closure lemma required by the commutativity dependency graph.

The final artifact is a newly authored closed theorem:

`∀m,n. Nat(m) → Nat(n) → m+n=n+m`.

Its intended proof is genuinely inductive and requires earlier lemma vellums. Commutativity is never exposed as a general replacement rule.

This culture reconnects proposition structure, nested second-order comprehension, first-order wires, equality, named definitions, explicit lambda terms, βη conversion, term-specific equality mechanics, relational typing, fixed points, vellum planning, and timeline exploration. It is the readiness gate for future cultures involving lists, trees, order, algorithms, or algebraic structures.

## 9. Mechanic coverage contract

| Mechanic | First honest curricular home |
|---|---|
| Double-cut introduction/elimination | Apprenticeship |
| Insertion/erasure | Apprenticeship and outer propositions |
| Iteration/deiteration | Early propositional contraction |
| Timeline scrubbing/branching | Apprenticeship |
| Exact vellum manifestation/dissolution | Apprenticeship demonstration; strategic use thereafter |
| Arity-zero comprehension | Early outer propositions |
| Vacuous bubble introduction/elimination | Nested proposition binders |
| Wire join/sever | First-order identity |
| Arity-one/two and open comprehension | First-order and relational systems |
| Relation fold/unfold | Relational systems |
| Closed-term introduction | Lambda grammar |
| Fusion/fission | Lambda producer/consumer structure |
| βη conversion/normalization | Lambda computation |
| Congruence join | Term equality |
| Endpoint transport | Term equality with closed evidence |
| Head strip | After head-normal-form literacy |
| Finite conversion certificate for divergent terms | Fixed-point foundations |

Before content freeze, the implemented player-action surface must be mechanically compared with this matrix. No surviving expert shortcut may remain untaught.

## 10. First implementation slice

The approved development order is a permanent seven-artifact opening batch, then completion of the overall game interface, then most remaining artifact authorship. It is not immediate authorship of the entire roadmap.

It includes:

- the sole game entry point and game-native product architecture;
- backward-only puzzle sessions and blank completion;
- progression, local save, and exact vellum authority;
- the curator's desk, main lens, timeline lever, teacher dialogue, red thoughts, and clean construction loupe;
- six permanent artifacts beginning the oldest pure-propositional culture;
- one permanent gateway artifact beginning the next proposition-binder culture;
- a required mastery spine alongside at least one elective artifact, so the interface proves non-linear progression;
- the full curriculum and mechanic graph as the durable authoring roadmap.

Later cultural content must not appear as placeholder, locked empty panels, or unverifiable scaffolding in the shipped slice. Non-shipping development fixtures may exercise interface surfaces whose instructional culture has not yet been authored.

## 11. Validation

### 11.1 Logical and content validation

- Every shipped theorem is closed and has an empty boundary.
- Every witness replays backward through exposed game actions to canonical blank.
- Every advertised mechanic is load-bearing in at least one representative assessment.
- Exact vellum dependencies are acyclic and audited for shortcuts.
- The prerequisite graph is acyclic, reachable, and free of overloaded or orphan nodes.
- Representative spikes establish feasibility before phase sizes are committed.
- Formal relational type translations and Boolean/Nat definitions are mechanically checked.
- Fixed-point content uses finite certificates rather than divergent normalization.

### 11.2 Runtime validation

- TypeScript typecheck.
- Kernel and game unit tests.
- Architecture-boundary tests.
- Catalog, fingerprint, prerequisite, and save-version tests.
- Timeline retained-future and branch-truncation tests.
- Exact vellum manifestation/dissolution tests.
- Construction-loupe geometry and unchanged behavior tests.
- Playwright novice-path playthroughs.
- Responsive rendered evidence for desktop and compact desk arrangements.
- Mechanical checks proving proof-assistant entry points, direction modes, authoring, external libraries, and import/export are absent.

### 11.3 Human validation

Kernel verification proves soundness, not learnability or fun. Novice playtests must separately evaluate:

- whether players predict move legality rather than trial every action;
- whether they recognize skills in unfamiliar diagram topology;
- where first meaningful moves stall;
- error categories and hint depth;
- whether teacher dialogue becomes intrusive;
- whether vellums create planning rather than one-move deletion;
- whether diagrams remain readable at realistic scale;
- whether players can transfer a skill after intervening content.

## 12. Explicit exclusions

- Forward proving.
- Two-front or meet-in-the-middle proving.
- Open or boundary-bearing game theorems.
- General theorem-rewrite controls or bundled open/general theorem content.
- User-authored goals, relations, theories, or theorem declarations.
- Theory folder/file loading, saving, import, or export.
- Proof-assistant shell, modes, compatibility adapters, or sibling application.
- Formal-logic prerequisites in player-facing instruction.
- Forced cursor scripts or mandatory intentional mistakes.
- Unproved relational typings for fixed-point combinators.
- Conversion of the incumbent theorem corpus into game content.
