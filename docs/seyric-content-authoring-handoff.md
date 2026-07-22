# Seyric Puzzle Content Authoring Handoff

## Role and scope

Create and refactor the Seyric puzzle content for Cursebreaker according to the product requirements below.

This is a content-authoring task only. Do not change proof physics, implement or audit user-facing mechanics, redesign the interface, launch Electron, package the application, modify `main`, merge branches, or run the dedicated physics battery. Work in the existing game worktree and preserve unrelated changes.

## Outcome

Produce a full, worthwhile collection of Seyric puzzles derived from the logic domain and the player experience each puzzle creates.

The collection must:

- provide substantial practice outside the mandatory progression path;
- use only a small mandatory progression spine;
- cover each worthwhile Seyric concept independently and in meaningful combinations;
- contain no padding, canonical duplicates, functionally redundant variants, or inappropriate higher-order logic;
- treat every puzzle as an open-ended problem solvable by any valid method;
- remain reusable, data-driven content rather than logic embedded in engine code.

Inventory size is not a design authority, success criterion, preservation constraint, or reporting requirement. Do not calculate, target, preserve, normalize, replace, or report a puzzle count.

## Mandatory progression and practice

The mandatory Seyric puzzles are exactly the minimal transitive set of Seyric puzzles that must be completed to unlock the first Myratic puzzle. Every other Seyric puzzle is practice. Nothing else makes a puzzle mandatory or practice.

Do not add a separate required-or-optional classification authority. Encode only the real progression graph: the first Myratic unlock condition and the prerequisite edges needed to satisfy it. Derive the mandatory Seyric set from that graph.

A puzzle's concepts, difficulty, guidance, artifact, coverage mapping, or value as practice do not independently affect this definition. Practice puzzles may have their own prerequisites and may support other practice puzzles, provided no path to the first Myratic unlock depends on them.

For every puzzle on the mandatory path, record the exact unlock or prerequisite edge that places it there. Remove any edge that is not necessary to unlock the first Myratic puzzle.

## Puzzle philosophy

These are problems, not riddles and not a curriculum.

Do not manufacture a unique intended solution. Alternative solutions are desirable. Do not constrain a starting diagram merely to prevent shortcuts or force a prescribed instructional sequence.

A validation witness proves only that a puzzle can be solved. It is not:

- an intended solution;
- a shortest solution;
- a required route;
- a completion definition;
- a reason to reject alternative solutions.

The teacher can explain an idea directly. A puzzle therefore does not need to force the player to discover one exact move.

Do not reduce a concept to a minimal representative. Players need meaningful variation, structural recognition, and mixed application. Conversely, do not create superficial variants merely by increasing operand count or making an expression longer.

For example:

- `∀X. X ∨ ¬X` provides the basic excluded-middle form.
- `∀X Y Z. X ∨ Y ∨ Z ∨ ¬(X ∨ Y ∨ Z)` provides meaningfully different practice recognizing excluded middle around a compound expression.
- Extending the compound example with another variable adds no meaningful new demand and is padding.

For every family of similar puzzles, identify the new visible proof situation, structural-recognition demand, interaction, or concept combination contributed by each puzzle. Remove a puzzle when its only distinction is superficial size or notation.

## Concept granularity

Analyze each topic independently before deciding what content it warrants. Do not derive the collection from an inventory template or allocate content slots in advance.

Do not collapse separate skills into a vague category. In particular:

- exchange and reassociation are separate;
- reassociation warrants several meaningfully different proof situations;
- weakening, projection, and injection are separate;
- weakening, projection, and injection also need worthwhile combined applications;
- excluded middle and Peirce are separate classical problems, not one generic capstone.

After providing adequate standalone exposure, include problems that mix concepts appropriately. A mixed puzzle must require the player to coordinate genuinely different ideas, not merely contain unrelated structures beside one another.

Review the complete Seyric propositional domain, including:

- primitive proof operations;
- structural recognition;
- exchange and reassociation;
- weakening, projection, and injection;
- constructive propositional transformations;
- factoring and distribution;
- De Morgan reasoning;
- reductio and contrapositive reasoning;
- case analysis and consensus-style reasoning;
- excluded middle and other classical principles;
- meaningful combinations across these areas.

Inspect the actual pure-propositional proof engine, current content data, and relevant game design documentation to understand the domain. Treat existing puzzle records as candidate material, not as inventory authority. Each candidate survives only if its proof situation makes an independent, worthwhile contribution.

## Seyric logic boundary

Seyric puzzles must stay within the pure propositional layer. Every production
start has exactly one ordinary outer goal cut, followed by an optional
uninterrupted prefix of arity-zero bubbles, followed by a matrix containing only
atom marks and ordinary cuts. The matrix contains no bubbles or wires, and every
atom is owned by one of the outer-prefix bubbles. Equivalently, its authored
logical shape is `∀X,Y,Z,… . P(X,Y,Z,…)`, where `P` contains no quantifiers.

Those outer bubbles close global proposition names. Identifying which global ring
owns each proposition occurrence and removing the prefix as terminal vacuous
cleanup are Seyric content. A feasibility witness may remove only the contiguous
prefix, deepest first, after all propositional work, with only trailing double-cut
cleanup afterward. Nontrivial local bubble placement, scope, introduction,
movement, distribution, and other quantifier reasoning belong to Myratic.

Do not include puzzles whose reasoning nontrivially quantifies over propositions, predicates, formulas, proof rules, or other second-order objects. That material belongs to Myratic content.

This is a restriction on authored starts and validation witnesses, not on the
logical moves exposed to the player. Do not remove or disable any player move to
enforce the content boundary.

Assume the game will expose the complete pure-propositional interaction set. Do not:

- decide whether a proof move is currently user-facing;
- audit or port mechanics from `main`;
- remove content because the current interface does not expose something;
- redesign interactions;
- restrict content around the current implementation state.

Those concerns are outside this task.

## Candidate evaluation

Read all existing Seyric puzzle data as candidate material. Retain, revise, or discard each candidate solely according to whether it contributes worthwhile, nonredundant Seyric content. Existing material receives no presumption either for or against inclusion.

Author additional puzzles whenever the first-principles review reveals:

- inadequate standalone exposure;
- inadequate practice variation;
- missing structural-recognition experience;
- missing mixed applications;
- an unjustified gap between simpler and more complex uses;
- a concept represented only by an unsuitable puzzle.

Do not ask permission merely to author additional content when one of these defects is present. Do not describe new content as filling or replacing inventory slots. There are no slots to preserve.

## Deduplication and direct quality review

Use the engine’s authoritative logical canonicalization to fingerprint every starting diagram.

Canonical duplicates must be consolidated or removed. Puzzle names, prose, guidance, artifact metadata, and witnesses must not affect logical identity.

Also compare Seyric matrices modulo the names and order of their harmless global
prefix while preserving the number of binders. Starts with the same binder
cardinality and atom/cut topology under such a permutation are redundant even
when their exact canonical fingerprints differ; adding or removing a vacuous
binder is a distinct interaction, not an ordering permutation. A deliberately
retained start whose matrix contains a direct cut and a sibling subset exactly
matching that cut's complete contents must have one unique approved
`immediateComplementPattern` in Seyric coverage; no two such starts may claim
the same pattern. Exact means playable graphical occurrence identity: canonical
extracted pattern plus binder attachments. Do not normalize through De Morgan,
double negation, distribution, or another proof transformation in this audit.

Canonical uniqueness is necessary but insufficient. Conduct a human adversarial review for functionally redundant puzzles and padding. Canonically distinct starts can still provide effectively identical player experiences.

Every retained puzzle must receive a direct review answering:

- What proof situation does the player actually see?
- Which ideas can naturally be exercised in that situation?
- What does the puzzle add beyond its nearest neighbors?
- Is that addition substantial enough to justify retaining it?
- Is it valid pure-propositional Seyric content?
- Does the first Myratic unlock graph require it, or is it practice outside that graph?
- Does a feasibility witness replay successfully through the real engine?

Automatic schema checks, replay validation, and canonical hashing do not substitute for this content review.

## Parallel authoring and adversarial review

Use isolated subagents in parallel for coherent concept families. Do not divide work into arbitrary numeric batches.

Give every author the same requirements:

- open-ended problems;
- no intended-solution enforcement;
- substantial practice outside the mandatory progression path;
- a small mandatory progression spine;
- a strict propositional Seyric boundary;
- no inventory quota;
- no padding;
- no reasoning about current user-facing mechanics.

Use different subagents for adversarial review so authors do not approve their own work.

Perform:

- a logical review covering validity, closedness, propositional purity, artifact availability, and witness replay;
- an experiential review covering meaningful variation, practice quality, concept combinations, padding, near-duplicates, and mandatory-graph justification;
- a whole-collection review covering missing practice, cross-family redundancy, progression gating, and canonical duplication.

Reviewers must inspect the actual proof situations. Running pre-existing automatic tests is not a substitute for reviewing the content.

## Data ownership

Keep content in the existing data-driven ownership model:

- Puzzle core owns the stable ID and logical starting diagram.
- Progression owns culture, folio order, explicit prerequisites, gateways, and unlocks. These edges are the sole authority for whether a puzzle lies on the mandatory path.
- Catalog owns artifact identity, title, and provenance.
- Guidance owns authored teacher pages, completion commentary, and exact recognized-state commentary.
- Coverage evidence owns concept mappings and review rationales and remains build-time evidence.
- Validation sidecars own feasibility witnesses, artifact-availability evidence, observed witness rules, and recognized-state demonstrations.

Do not put any of the following into puzzle cores:

- completion semantics;
- logic profiles;
- verified-witness declarations;
- teacher-system ownership;
- presentation parameters;
- curriculum roles;
- performance IDs;
- intended solutions.

Puzzle completion is determined universally by the engine. Witnesses are validation evidence only.

Coverage metadata must never generate puzzles, determine progression order, or place a puzzle on the mandatory path.

## Teacher guidance

Teacher content is separate from the logical puzzle contract.

Where guidance is authored:

- present it as a passive, unobtrusive edge note;
- never require the player to read it;
- allow several pages;
- keep every page to a single paragraph;
- make page advancement optional;
- never interrupt play with a modal;
- do not add generic timed hints or stalled-player behavior.

Across the opening Seyric spine, stage the basic interaction guidance on the first
real proof situations that exercise it. On `two-veils`, author separate pages explaining:

- noticing highlighting;
- selecting;
- deselecting;
- clearing a selection;
- the proof move that completes the puzzle.

The completing move belongs on the final page. Explain timeline rewind and branching
on `forked-veil`, where the sibling erasure supplies an actual branch to revisit.
Earlier pages must remain available without blocking interaction. Most later guidance
should be concise, and puzzles do not need guidance merely because they exist.

## Validation

Before reporting completion, prove that:

- every production puzzle has a complete data bundle;
- every feasibility witness replays through the real backward-proof engine;
- every Seyric start is closed and purely propositional;
- canonical start fingerprints are unique;
- every retained puzzle has a substantive human review rationale;
- each concept has adequate standalone practice and meaningful mixed applications;
- the mandatory Seyric set is exactly the minimal transitive prerequisite closure needed to unlock the first Myratic puzzle;
- every puzzle on that path has a concrete unlock or prerequisite edge, and no unnecessary edge enlarges the path;
- no separate required-or-optional declaration competes with the actual progression graph;
- artifact-dependent witnesses use only artifacts available through valid prerequisite closure;
- progression, catalog, guidance, coverage, validation, and puzzle cores agree;
- Vite derives runtime availability from the approved content directories, while
  manifest registration and ordering remain mandatory;
- discarded content has no production registration, alias, tombstone, adapter, or compatibility path;
- no inventory quota, replacement authority, or normalization authority controls the collection;
- content validation, focused tests, type checking, and the renderer build pass.

Do not launch Electron. Do not run the dedicated proof-physics battery.

## Final report

Report:

- the mandatory Seyric path and the exact Myratic-unlock or prerequisite edge placing each puzzle on it;
- the practice outside that spine provided for every concept family;
- meaningful variations within each family;
- mixed-concept coverage;
- canonical duplications discovered and resolved;
- functionally redundant or padded content discovered and removed;
- content authored or revised because review found inadequate practice;
- inappropriate non-Seyric content removed;
- validation commands and exact results;
- any unresolved content defects.

Do not calculate or report inventory size. Do not describe inventory size as a target, observation, baseline, comparison, or accomplishment.
