# Opening Cultures and Content Design

**Status:** Approved  
**Date:** 2026-07-11

## Outcome

Cursebreaker ships an initial batch of seven permanent artifacts before the
overall interface is completed: six artifacts beginning the oldest
pure-propositional sealing culture and one gateway artifact beginning the next
proposition-binder culture. The batch supplies authentic content for culture
navigation, required and elective progression, teaching, proof sessions,
completion, timelines, the construction loupe, and saves without sampling
later tutorial mechanics out of order.

Most artifact production follows after the interface is substantially final.
The full tutorial nevertheless spans several cultures and continues through
approximately the fixed-point theorem.

## Cultures are the puzzle genres

Each puzzle genre is diegetically a culture's sealing tradition. Cultural age,
lineage, contact, and isolation explain why its artifacts use particular
representations or have unusual mechanical habits. The opening culture is the
oldest surviving and most structurally primitive tradition, making its simple
seals a natural instructional starting point.

A culture record owns:

- stable internal identity;
- relative historical layer;
- lineage and isolation facts where known;
- artifact prerequisites that unlock the culture;
- curator-facing description;
- characteristic sealing vocabulary.

These are catalog and worldbuilding facts, not decorative labels. The later
visual naming and materials pass must demonstrate coherent cultural options
before production aesthetics are selected.

## Non-linear progression

Cultures and artifacts form one prerequisite DAG. An artifact is required when
it lies in the prerequisite closure of locked artifacts or a culture gateway.
Every other artifact is elective. Requiredness is derived from graph structure,
not stored as a second flag that can disagree with the graph.

Unlocking another culture leaves earlier elective artifacts available. An
elective artifact is complete authored content for additional practice,
retrieval, remediation, or challenge; it is not filler and is not visually
presented as inferior.

The initial graph is:

```text
artifact 1 → artifact 2 → artifact 3 → artifact 4 → artifact 5
                                                        ├─→ artifact 6 (elective)
                                                        └─→ unlock culture 2
                                                              → artifact 7
```

Artifact 5 is the development-time first-culture gateway. When the full first
culture is authored, the gateway may move to a later transfer artifact without
changing the seven artifacts themselves.

## Artifact naming

Player-facing artifact names use a dual professional register:

1. A proper name grounded in function, culture, location, maker, owner,
   discoverer, excavation, or catalogue history.
2. Optional curator shorthand describing a visible seal morphology.

Important gateways, discoveries, and capstones receive memorable professional
names. Routine elective practice may use plainer excavation or accession names.
Formal theorem names never become display titles merely because they are
convenient mathematical labels.

Culture and artifact names may mutate the real-world concepts that inspired
their formal content, including through non-English linguistic roots. Exact
names must be brainstormed as one coherent cultural naming pass during
implementation. The descriptive labels below are authoring shorthand, not
approved display names.

## Learning metadata

Every artifact records:

- culture and artifact prerequisites;
- exact closed zero-boundary goal and verified backward witness;
- stable performance identities introduced, practiced, retrieved, and assessed;
- proof mechanics used by the witness;
- authored teacher beats;
- misconception categories for thought feedback;
- vellum eligibility;
- professional name, curator shorthand, and provenance metadata.

Teacher instruction states the immediate visible affordance briefly, then
returns control. No artifact requires an intentional mistake, a prescribed
solution order where alternatives are legal, or a mandatory timeline detour.

## Initial seven artifacts

### 1. `¬¬⊤`

Authoring shorthand: **Two Veils**. Introduces eliminating one paired cut.
Teacher copy identifies the removable pair without scripting the gesture.

Verified backward witness: one double-cut elimination.

### 2. `¬¬¬¬⊤`

Authoring shorthand: **Four Veils**. Practices repeated elimination. The two
valid orders provide a natural opportunity to introduce timeline scrubbing and
branching without forcing either route.

Verified backward witness: two double-cut eliminations.

### 3. `¬(¬⊤ ∧ ¬⊤)`

Authoring shorthand: **Forked Veil**. Introduces backward erasure: one sibling
blocks the familiar collapse, so the player removes it and retrieves the prior
move.

Verified backward witness: erasure, then double-cut elimination.

### 4. `¬(¬⊤ ∧ ¬¬⊤)`

Authoring shorthand: **Echoed Veil**. Introduces deiteration through a nested
copy supported by an older matching form, contrasts it with erasure, and then
retrieves double-cut elimination.

Verified backward witness: deiteration, erasure, double-cut elimination.

### 5. `∀P.P→P`

Authoring descriptor: **single-mark return form**. This artifact transfers the
preceding spatial pattern to one universally bound proposition mark. Instruction
explains visible mark ownership without requiring formal-logic vocabulary.

Verified backward witness: deiteration, erasure, vacuous-bubble elimination,
double-cut elimination.

### 6. `∀P,Q.(P∧Q)→P`

Authoring shorthand: **One of Two**. This elective artifact provides varied
practice with two universal binders and selective removal while retrieving the
preceding pattern.

Verified backward witness: deiteration, two erasures, two vacuous-bubble
eliminations, double-cut elimination.

### 7. `∃P.P`

Authoring shorthand: **The Unwritten Name**. This is the required first artifact
of the second culture. It isolates non-universal proposition quantification and
the construction loupe: instantiate the proposition with the blank sheet.

Verified backward witness: one arity-zero comprehension instantiation.

## Catalog authority and validation

The generic title-only campaign model is replaced by culture authority. No
campaign alias or parallel campaign/culture concept remains. Catalog build must
reject:

- missing or cyclic culture and artifact dependencies;
- unreachable cultures or artifacts;
- open goals or witnesses that do not reach canonical blank;
- learning or mechanic claims contradicted by the witness;
- missing professional name, provenance, teacher, or misconception structure;
- culture metadata insufficient to identify its historical layer and sealing
  vocabulary;
- bundled content importing prototype theories or requiring unavailable player
  interactions.

Progression derives unlocked cultures, unlocked artifacts, and currently
required artifacts solely from the verified catalog plus completed identities.
Save fingerprints include culture and learning metadata so incompatible content
drift is rejected rather than guessed through.

## Scope boundaries

- No visual culture direction, final names, or final dialogue is invented
  without its dedicated implementation-time review.
- No existential puzzle appears in the first culture.
- No first-order wire, equality, lambda, or later tutorial mechanic appears in
  this batch.
- No game-only proof interaction is introduced.
- No placeholder later culture is included in the shipped catalog.
- Non-shipping test catalogs may exercise future interface surfaces.
- Physics and physics validation are outside this content phase.

## Validation evidence

A pre-production spike replayed every proposed witness through the real kernel
in backward orientation and reached canonical blank: 1, 2, 2, 3, 4, 6, and 1
steps respectively. Production tests must reconstruct that evidence from the
bundled catalog, validate the culture/artifact graph and elective derivation,
round-trip saves after migration, and keep the game architecture boundary clean.
