---
name: visual-proof-assistant-design
created: 2026-06-10T00:42:35Z
updated: 2026-06-10T00:42:35Z
status: draft-for-user-review
---

# Visual Proof Assistant — Design Specification

A visual proof assistant for a second-order variant of Peirce's existential graphs over untyped λ-expressions. Diagrams are the syntax; proof is graph transformation; λ-terms render as Tromp lambda diagrams bent into incomplete circles; everything on screen behaves like a physical object, and no physical interaction can ever change what a diagram says.

Authority note: semantics and user-facing behavior in this document were confirmed by the user. Internal representations, algorithms, and code organization are engineering choices made by the implementer; they are open to revision at any time provided the semantics and user-facing behavior are preserved, and they are never to be defended by appeal to user approval.

The three projects under `Old/` are abandoned and are not references for any implementation decision. This system is designed from first principles.

---

## 1. Hard constraints

1. **Three-layer separation.** (a) *Abstract syntax/semantics*: the saved diagram structure; the only thing the kernel, rules, and matching ever see. (b) *Rendering*: a pure function of abstract syntax plus ephemeral interaction state. (c) *Physics*: reads structure and geometry, writes only geometry. No layer reaches upward.
2. **Physics is never semantic and never saved.** Saved files contain zero physics and zero layout: no positions, sizes, velocities, bend parameters, pins, or camera state. Layout is derived automatically on load.
3. **Physical interaction cannot change structure.** No force, collision, or drag can detach a wire, move an item across a region border, or merge/split anything. Structural change happens only via explicit edit actions (Edit mode) or rule applications (Proof mode).
4. **Soundness is kernel-local.** Only the kernel transforms asserted diagrams. Every transformation is a foundational rule or a stored rule whose derivation the kernel checked at declaration time.
5. **No heuristics.** Matching is complete (finds a match iff one exists). Every threshold or constant in any layer has a written, principled justification. Resource limits (normalization fuel) are explicit, user-visible, and never silently change logical outcomes (§3.7).
6. **No silent failures.** Every failed check, failed match, exhausted fuel budget, or broken dependency is reported loudly and specifically.

## 2. The logic — semantics

### 2.1 Domain and judgements

The domain of individuals is untyped λ-terms. The logic is classical second-order logic over this domain, presented as existential graphs: a diagram asserts a proposition; the blank sheet asserts truth; juxtaposition in a region is conjunction; a *cut* (negation boundary) negates its contents; parity of cut nesting makes a region *positive* (even number of enclosing cuts) or *negative* (odd). Second-order bubbles are quantifiers and do **not** affect parity — only cuts do.

### 2.2 Diagram constituents

- **Regions** form a tree: the root *sheet*, *cuts*, and *second-order bubbles*. A bubble binds one fresh relation variable and carries one declared field: its **arity** n ≥ 0. Quantifier force (∃ vs ∀ as read from the sheet) is derived from parity, never stored.
- **Term nodes** carry a λ-term over the grammar `Term ::= BVar | Port | Const | Lam Term | App Term Term` (de Bruijn internally; binder names do not exist in the abstract syntax). A node has one **output** port plus one port per distinct free variable (`Port` ref). **Semantics: the node asserts the constructor relation `output = term(free vars)`** — exactly as `x = f(y,z)` is a ternary relation for a first-order constructor `f`, `x = λf. f y z` is a ternary relation among x, y, z. `Const` refs name definitions (always closed terms).
- **Wires** are hyperedges among ports: one wire = one line of identity = one existentially scoped individual. A wire belongs to a *scope region*; every endpoint lies in that region or a descendant (this is how a line of identity reaches into cuts while its quantifier scope stays put). Wires may have any number of endpoints, including zero or one (bare "something exists"). There is no separate spider object; a multi-branch junction is a wire with >2 endpoints, and branch points are rendering.
- **Relation atoms** are the only non-equational predicate form: an atom references an ancestor bubble (its binder) and has n ordered argument ports, n = the binder's declared arity. Relation variables are a separate syntactic category from terms; they cannot occur inside λ-terms. This is enforced by the grammar itself.
- **Diagrams-with-boundary**: a diagram plus an ordered list of dangling wire stubs. One concept serving three roles: rule-statement sides (LHS/RHS share a boundary), comprehension instances for the second-order rules, and named-relation definition bodies. *A relation is a diagram with a boundary*; λ-constructor nodes are one atomic species of relation.

Equality of terms is βη-convertibility. Equality of diagrams is structural identity up to canonical form (§4.3); wire identity (which ports share a wire) is the semantic content, wire geometry is not.

### 2.3 Quantification

First-order quantification is wire scoping, as in beta graphs: a wire scoped in a positive region is an existential, in a negative region a universal (read from the sheet). Second-order quantification is the bubble: a bubble in a positive context is ∃X over n-ary relations on λ-terms, in a negative context ∀X. Instantiation is **full graph comprehension**: any diagram-with-boundary of matching arity is an admissible relation.

## 3. The logic — rules

### 3.1 Foundational rules

These are the only unjustified rules. Each is a single kernel primitive and a single user action. Exact side conditions for every primitive get a written soundness argument in the kernel documentation and dedicated tests before implementation is considered complete.

1. **Insertion** — draw any well-formed subgraph into a negative region; includes joining wires there (merging two wires into one).
2. **Erasure** — delete any subgraph from a positive region; includes severing wires there (splitting a wire's endpoint set).
3. **Iteration / Deiteration** — copy a subgraph from region r into r or any descendant not inside the copied subgraph, with the copy's boundary attaching to the same wires (extending them inward); inversely, remove any subgraph that iteration could have produced.
4. **Double cut** — introduce or eliminate a nested pair of cuts with nothing in the annulus between them (wires may pass through the annulus).
5. **βη-congruence** — replace the term in a term node by any βη-convertible term. Ports adjust: a free variable present in both terms keeps its wire endpoint; a dropped variable detaches its endpoint (sound: conversion preserves the asserted relation, and a variable absent from the result was unconstrained); a newly appearing variable (necessarily value-irrelevant) gets a fresh singleton wire in the node's region. Never stepped manually by the user (§3.7).
6. **Fusion / Fission** — when a wire's endpoints are exactly {node A's output, node B's port p}, both nodes in the wire's scope region, replace A and B by one node whose term substitutes A's term for p in B's term (ports merged accordingly); inversely, factor any subterm out into its own node. Equational; any region.
7. **Unfold / Fold** — replace a `Const` occurrence by its definition body or vice versa, inside any term node. Equational; any region; never automatic.
8. **Comprehension (second-order)** — the polarity-directed rewrite between `φ[P]` and `∃X φ[X]`: in a positive context, the user selects a subgraph φ and a concrete relation P (any diagram-with-boundary, arity n); a fresh bubble is wrapped around φ and chosen occurrences of P within it are replaced by atoms of the new variable (existential generalization / witnessing). In a negative context, the inverse: a bubble is eliminated by replacing each of its atoms `X(t̄)` with a copy of a chosen P plugged onto the arguments, the bubble border dissolving into its parent region (universal instantiation, as read from the sheet). The zero-occurrence case gives vacuous bubble introduction/elimination.

Rules 1–4 are the classical beta-graph rules; 5–7 are the equational layer for the constructor semantics; 8 is the standard second-order quantifier rule pair with full comprehension.

### 3.2 Derived rules — justify once, use natively

A derived rule is declared by finishing a proof of its statement. The kernel checks the derivation **once, at declaration time**; thereafter the rule is a first-class object applied by matching its *statement* — its derivation is never expanded, not in interaction, not in proofs, not in replay.

- **Statement form**: LHS and RHS, two diagrams-with-boundary over a shared boundary.
- **Equational rules** (every proof step was an equivalence): apply in either direction in **any** region.
- **Directed rules** (some step was one-way): apply forward (LHS→RHS) at positive match sites, backward at negative sites — the standard polarity discipline of deep inference, and the same discipline rule 8 follows.

### 3.3 Definitions

Two kinds; both conservative (no proof obligation), both yielding fold/unfold and a palette entry. Display names are presentation metadata in the theory, not part of diagram structure.

- **Term constants**: a name for a closed term (`0`, `succ`, `+`). Folded form renders as a named disc.
- **Named relations**: a name for a diagram-with-boundary (`ℕ(_)`, `_ ≤ _`). Folded form renders as an atom-like node with n ports; unfolding splices the body onto the argument wires. This is how `ℕ` stays one node on screen while its second-order definition lives inside.

### 3.4 Conjectures and proofs

A conjecture is authored as **LHS ⟹ RHS** over a shared boundary. A *theorem* (a statement true outright) is the special case where LHS is the blank sheet: proving `blank ⟹ T` establishes T, and the resulting rule lets T be scribed into any positive region thereafter — the classical existential-graph treatment of proven theorems.

Semantically, every finished proof is one directed chain: a sequence of rule applications carrying LHS to RHS, each step sound in the direction it is applied. The finished proof classifies itself: all-equational steps → equational rule; otherwise → directed rule. Declaring the proved statement as a rule is one action.

**Proof construction is explicitly bidirectional.** Both modes are supported and freely mixable within one proof:

- **Forward**: start from LHS and construct toward RHS — each step applies a rule in its sound direction, building up what is true. For theorems this is reasoning from the blank sheet outward.
- **Backward**: start from RHS (the goal) and reduce it — each step applies a rule *in reverse*, and the kernel checks that the step is sound when read forward (so polarity conditions appear flipped to the user: e.g., backward erasure is forward insertion). For theorems this is rewriting the goal down to the blank sheet.
- **Meet in the middle**: grow a forward frontier from LHS and a backward frontier from RHS; the proof completes when the two frontiers coincide up to canonical form.

Whatever the construction order, the stored proof object is normalized to a single forward chain (forward segment + reversed backward segment). Replay and verification are therefore direction-agnostic, and playback can be watched in either direction.

A proof object records: initial diagram, ordered steps (rule reference + match instantiation in canonical addressing), final diagram, and the content fingerprints of every definition and rule it uses. Steps replay deterministically.

### 3.5 Theories

A theory is an append-only dependency DAG of definitions, derived rules, and proofs. Opening a theory re-verifies every justification exactly once, cached by content fingerprint; a dependency that has drifted breaks loudly, identifying what broke and why.

### 3.6 Verification

Binary: a stored artifact is *verified* or *broken*. No intermediate status exists.

### 3.7 Deduction modulo βη

Conversion is the congruence the system works modulo, not a rule the user steps through.

- **Matching is modulo βη**: a rule applies wherever its statement matches up to conversion of term-node contents; the system finds the match itself.
- **Normalize** is a single user action on any term node (rule 5 with the normal form).
- **Honesty under undecidability**: βη-equivalence of untyped terms is undecidable. Interactive equality checking uses bounded normalization (normalize-and-compare under an explicit, user-visible fuel setting). When fuel runs out the system says so, specifically, and accepts an explicitly constructed finite reduction path as a conversion certificate instead (this is how `Y f = f (Y f)` is established despite `Y f` having no normal form). It never silently fails and never pretends.
- **Recorded steps store their conversion certificates** (normal forms reached, or reduction paths, with step counts). Replay checks certificates and never re-searches — so replay is exact, deterministic, and fuel-independent. Fuel affects interactive search only; it can never change whether a stored proof verifies.

## 4. Architecture (engineering)

### 4.1 Platform and stack

Single-user, local-first browser application. TypeScript throughout, minimal dependencies (build tooling: Vite; tests: Vitest; no UI framework, no runtime dependencies in the kernel). The world renders to Canvas2D with a thin HTML overlay for chrome. These are implementer's choices, revisable.

### 4.2 Packages

```
kernel/      pure, headless, zero DOM imports: abstract syntax, validation,
             canonicalization, conversion engine, matching, the eight
             foundational primitives, derived-rule checking, proof replay
theory/      theory store: definitions, rules, proofs, dependency DAG,
             fingerprint cache, (de)serialization of the semantic file format
layout/      deterministic initial layout + the force simulation
             (reads kernel structures + geometry, writes geometry only)
render/      Canvas2D drawing: Tromp bending, visual language, animation
app/         shell, modes, interaction, undo/redo, file handling
```

Dependency direction is strictly downward in this list; `kernel/` and `theory/` import nothing from the rest and run under Node for tests. The build fails if a forbidden import appears (enforced mechanically, e.g. dependency-cruiser or an equivalent check in CI).

### 4.3 Kernel design requirements

- Immutable diagram values; every primitive takes a diagram + parameters and returns a new diagram or a specific error.
- Well-formedness (wire scope validity, atom-binder ancestry, arity agreement, port-term consistency) is checked at construction; invalid diagrams are unrepresentable through the public API.
- **Canonicalization**: a deterministic, documented, structure-directed canonical form giving content fingerprints with the property: equal fingerprints iff isomorphic diagrams (terms compared up to de Bruijn). The exact algorithm is kernel documentation; it is exact, not a hash-and-hope heuristic.
- **Canonical addressing**: proof steps address their match sites via positions in the canonical form, so steps are stable across sessions and machines.
- **Matching**: given a diagram-with-boundary pattern and a region, enumerate occurrences modulo βη. Complete — a match is found iff one exists; anchor-driven backtracking keeps the common case fast, but no completeness-sacrificing pruning is permitted.
- **Determinism**: no wall-clock, no randomness anywhere in kernel or layout. Same inputs, same outputs, always.

### 4.4 Conversion engine

De Bruijn terms; normal-order reduction (leftmost-outermost, so a normal form is found whenever one exists) with explicit fuel; η-contraction; reduction paths as first-class certificate values that can be stored in proof steps and re-checked cheaply.

## 5. Rendering

Rendering is a pure function of (abstract syntax, ephemeral interaction state, geometry from the physics layer). Nothing rendered is ever semantic input.

### 5.1 λ-nodes: Tromp diagrams bent into incomplete circles

Confirmed scheme (option A of the explored alternatives):

- The flat Tromp diagram maps to polar coordinates: binder lines become concentric arcs with the **outermost binder forming the node's visible rim**; variable-use lines become radial segments running inward; application bars become inner arcs; structure grows toward the center. A node whose term has no top-level binder (e.g. `y z`) draws a faint neutral rim circle as its boundary instead; when binders exist, the outermost binder arc coincides with the rim.
- **Free-variable lines pierce the rim radially** and continue as wires — the node grows hooks toward its arguments, like a spot in a graph. Multiple occurrences of the same free variable converge to a single port.
- **The output emerges through the C-gap** (the incompleteness of the circle) from the application spine.
- Hover/zoom shows the flat, undistorted Tromp diagram as a detail view; bending is the at-rest presentation.

### 5.2 Visual language

- **Cuts**: smooth closed curves; **negative (odd-depth) regions are subtly shaded** so parity reads at a glance.
- **Second-order bubbles**: visually distinct closed curves wearing a small **arity badge** on the border.
- **Atom–binder rendering** (confirmed hybrid): each visible bubble owns a hue and its atoms wear it at rest; hovering or selecting an atom or bubble draws an explicit dotted **tether** to the binder and highlights all sibling occurrences. Color is never the only channel.
- **Folded definitions**: term constants render as named discs; named relations as atom-like nodes with their name.
- **Wires**: smooth curves routed around nodes; branch points drawn as small junctions (pure rendering of >2-endpoint wires).
- Mode, selection, applicable-rule highlighting, and match previews are overlay states, never structure.

### 5.3 Proof animation

Each rule application animates as a continuous morph of the physical objects: iteration visibly copies and floats the copy to its destination; erasure shrinks and fades; double-cut elimination collapses the two rings into each other; fusion slides two nodes together. Stored-proof playback is these animations in sequence — pausable, scrubbable both directions, speed-controllable. A reduced-motion setting collapses all transitions to instant.

## 6. Physics

- **Self-organizing, always settling**: the simulation continuously seeks equilibrium. Nodes have mass and damping; drags track with velocity; releases coast and settle; nothing teleports.
- Wires act as elastics (tension, slight sag, gentle tug on endpoints); regions are physical containers (contents ride along with damped follow, borders stretch under pressure and resize to fit, siblings shoulder apart to stay disjoint); λ-nodes rotate freely with inertia, and wire tension applies torque so they settle into low-kink orientations.
- **User placement is not a pin.** Dragging is a force; the system keeps seeking equilibrium afterward. An explicit *pin* action while dragging is available; pins are ephemeral session state.
- **Layout is never saved.** On load, a deterministic initial layout is computed from canonical structure, then the simulation settles it. Same file, same starting appearance.
- Every simulation constant ships with a written justification (mass/damping from settle-time targets, spacing from legibility minima); no tuned-until-it-looked-right values without documented reasoning.
- A drag that fights a constraint (e.g., pulling a node against its region border) stretches and snaps back; it never restructures.

## 7. Interaction and app shell

### 7.1 Shell — canvas-first

The diagram is a full-bleed world. Floating, collapsible chrome: an Edit/Prove mode switch; a left drawer holding the theory palette (definitions, rules, proofs); a floating proof timeline with scrubber during proving/playback; the proof **target as a pinnable picture-in-picture card, expandable to a side-by-side split** with diff highlighting. Resting state is always the world, not panels.

### 7.2 Edit mode (constructing diagrams)

Free construction constrained only by well-formedness. Confirmed interactions:

- **Term text entry**: type into a new node using `\` for λ (`\f.\x. f (f x)`); ASCII only; free variables become ports; names are discarded after parsing.
- **Graphical term building**: wire outputs into ports; **Fuse** collapses a composite into one node; **Split** factors a subterm out; **Abstract** closes a port by wrapping the term in a λ (edit-mode constructions, distinct from the proof-mode rule actions they resemble).
- **Cuts and bubbles**: select items, then a button/hotkey spawns the enclosure around the selection — the user explicitly chooses cut vs second-order bubble (with arity) at creation. No gesture inference.
- **Wires**: drag port→port; drag from a wire's body to branch it.
- **Atoms**: dragged out of their bubble's palette entry.
- Items may be dragged across region borders in Edit mode (the system states that meaning changed); never in Proof mode.
- **Definitions**: select a closed term node → *Define constant*; select a subgraph and order its dangling wires → *Define relation*.

### 7.3 Proof mode

The diagram changes only by rule application. A **direction toggle** selects which frontier the user is growing — forward (from LHS) or backward (from RHS), per §3.4 — and the picture-in-picture card always shows the opposite end. In backward mode, applicability highlighting shows where rules apply *in reverse*, with the kernel enforcing forward soundness of every step. Both interaction directions exist in either mode: select a subgraph → see every rule applicable there (matched modulo βη, automatically); or pick a rule → every match site lights up → click one. **Normalize** is one action on any term node. Undo/redo walks the step list of the active frontier. The proof completes when the frontiers coincide (or one reaches the other end), and finishing offers one-action rule declaration (§3.4).

### 7.4 Persistence

Theories save/load as ordinary files: text-based, diffable, git-friendly, semantic content only. Autosave (to browser storage) guards against tab loss. Opening a theory re-verifies its DAG with cached fingerprints (§3.5). Bundled example theories open on first launch.

## 8. MVP examples

**Demo pack — the λ-calculus as a playground:**

- Encodings library as definitions: booleans (`true`, `false`, `and`, `or`, `not`), pairs, Church numerals `0`, `succ`, `+`, `×`. `1 + 1 = 2` is three named nodes and a Normalize.
- Computation theorems (e.g., `and true x = x`): unfold + normalize; the modulo engine does the boring work.
- **Fixed-point theorem** `∀f ∃x. x = f x`: pure beta-graph statement, witness `Y f`; deliberately exercises the non-normalizing fallback via the reduction-path certificate `Y f →β f (Y f)`.

**Flagship — Frege-style arithmetic:**

- `ℕ(n)` as a named relation: "n is in every class containing 0 and closed under successor" (one arity-1 bubble in the body).
- **Induction as a derived rule**, justified once from unfolding ℕ + comprehension, then applied natively.
- Recursion laws of `+`: `m + 0 = m` falls to βη alone; `m + succ n = succ (m + n)` provably does **not** for open `m` — it requires induction. The seam between automatic-modulo-βη and genuine second-order reasoning lands exactly where the mathematics gets interesting.
- **Commutativity of addition** as the flagship proof: nested induction, derived rules applied by name, `+-comm` declared and replayable as animation.

## 9. Testing strategy (engineering)

- **Kernel first, headless**: every foundational primitive gets soundness tests (positive cases, parity-violation rejections, scope-violation rejections) plus property-based tests (round-trips: fuse/fission, fold/unfold, double-cut intro/elim; canonical-form invariance under primitive application where expected; fingerprint equality ⟺ isomorphism on generated diagrams). Tests are verbose and use no mocks anywhere.
- **Conversion engine**: normalization against known normal forms; certificate check/re-check round-trips; fuel-exhaustion paths assert loud, specific reporting.
- **Matcher**: completeness tests (planted matches must be found; absence must be reported), including matches that exist only modulo βη.
- **Theory store**: DAG verification, fingerprint caching, drift detection breaking loudly, file round-trips.
- **Replay**: every example proof replays from its file; mutating any dependency breaks the dependent proof, and the test asserts the specific break.
- **Layer separation**: mechanical import-boundary checks; a test asserting serialized files contain no layout/physics fields.
- **End-to-end**: headless-browser drives of the real UI for each foundational rule, definition flows, proof recording, playback, and save/load — the bundled examples double as the E2E corpus.
- Every feature lands with its tests in the same change, never deferred.

## 10. Out of scope for MVP

Multi-user/collaboration, mobile/touch-first interaction, theory imports/namespacing across files, proof search automation beyond bounded normalization, alternative term languages, WebGPU/3D rendering. Nothing in the design forecloses these; nothing in the MVP implements them.
