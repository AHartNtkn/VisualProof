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

The approved opening names use fictional archaeological exonyms built from a
shared ancient philological stratum. **Seyric** is distantly shaped by Greek
*sēma* (mark or sign); **Myratic** is distantly shaped by Greek *martys*
(witness). The mutations are background construction logic, not etymology
lessons shown to the player. Neither name identifies or borrows the name of a
living people.

The two exact culture records are:

- **The Seyric Horizon** — the earliest secure sealing horizon, known from
  funerary closures, threshold wards, and stone stoppers. Its self-name is
  unknown; “Seyric” is the modern archaeological exonym. The opening seals
  develop veils, fields, echoes, rings, and marks.
- **The Myratic Tradition** — the isolated Myrat complex, whose deliberate
  hollows may stand for complete seal-patterns. No direct Seyric lineage is
  established. Supplying a pattern is its first technique, not the identity of
  the whole tradition.

These exact names and the provisional curatorial vocabulary in the main game
design govern the initial content implementation. Later revision requires
playtest or worldbuilding evidence, not local synonym preference.

## Learning metadata

Every artifact records:

- culture and artifact prerequisites;
- exact closed zero-boundary goal and verified backward witness;
- stable performance identities introduced, practiced, retrieved, and assessed;
- proof mechanics used by the witness;
- authored teacher interventions for opening, completion, stalled play, or
  exact recognized proof states;
- broken-seal reference eligibility;
- professional name, curator shorthand, and provenance metadata.

Teacher instruction states the immediate visible affordance briefly, then
returns control. No artifact requires an intentional mistake, a prescribed
solution order where alternatives are legal, or a mandatory timeline detour.
Invalid-move thoughts are not artifact content: they are generated by the
interaction layer from authoritative move refusals. An artifact may instead
recognize a valid transition into an anticipated trap and initiate teacher
dialogue with recovery guidance. Each exact-state intervention includes a legal
demonstration trace so catalog validation can prove the state is reachable.
Early empty-cut dead ends are the canonical example.

## Opening performance graph

The initial catalog uses these exact stable performance identities. Each row's
clauses become ordered knowledge points; correction copy remains authoring
metadata for later hints rather than invalid-action thoughts.

| Identity | Performance | Prerequisites | Ordered knowledge points | Mastery evidence |
|---|---|---|---|---|
| `release-paired-veils` | Lift one eligible pair of veils without disturbing what it encloses. | none | The veils are directly nested; nothing lies between their boundaries; lifting them preserves enclosed content. | Independently identifies and lifts an eligible pair. |
| `resolve-repeated-veils` | Resolve a seal containing more than one eligible pair. | `release-paired-veils` | More than one pair may be eligible; either legal order may be used; lifting one pair may expose another. | Completes nested-pair practice without treating one valid order as mandatory. |
| `clear-dark-field` | Clear a complete fragment from an eligible dark field. | `release-paired-veils` | Clearing is allowed only in the appropriate field; the selection must be a complete fragment; clearing can expose an older paired form. | Clears only the necessary fragment and retrieves paired-veiling. |
| `lift-supported-echo` | Lift an exact repeated fragment supported by an older matching form. | `clear-dark-field` | The outer support must already exist; the echo must match exactly; lifting the echo leaves its support in place. | Distinguishes an exact supported echo from a merely similar fragment. |
| `trace-single-mark-ownership` | Trace one mark through veils to the ring that owns it. | `lift-supported-echo` | A ring owns matching marks throughout its interior; intervening veils do not change ownership; a ring dissolves only after it owns no marks. | Resolves the single-ring artifact while combining all earlier spatial skills. |
| `distinguish-nested-owners` | Keep marks belonging to nested rings independent. | `trace-single-mark-ownership` | Each ring owns only its corresponding marks; nesting does not merge owners; removing one owner's material must not capture or release another's marks. | Independently resolves the elective two-ring artifact. |
| `supply-complete-pattern` | Supply a complete pattern for a Myratic hollow. | `trace-single-mark-ownership` | A hollow may stand for an entire pattern; the blank sheet is a complete pattern; committing the loupe replaces every occurrence consistently. | Uses the construction loupe to resolve `∃P.P` with the blank sheet. |

Artifact learning roles are fixed as follows:

- artifact 1 introduces `release-paired-veils`;
- artifact 2 practices and assesses `release-paired-veils` and introduces
  `resolve-repeated-veils`;
- artifact 3 introduces `clear-dark-field` and retrieves
  `release-paired-veils`;
- artifact 4 introduces `lift-supported-echo`, practices `clear-dark-field`,
  and retrieves `release-paired-veils`;
- artifact 5 introduces `trace-single-mark-ownership`, practices
  `lift-supported-echo` and `clear-dark-field`, and retrieves
  `release-paired-veils`;
- artifact 6 introduces `distinguish-nested-owners`, practices
  `trace-single-mark-ownership`, and assesses the first culture's core skills;
- artifact 7 introduces `supply-complete-pattern` and retrieves
  `trace-single-mark-ownership` without claiming mastery of the later Myratic
  curriculum.

## Initial seven artifacts

### 1. The Seyr Ossuary Seal

- **Curator shorthand:** paired-veil form.
- **Formal goal:** `¬¬⊤`.
- **Provenance:** a basalt stopper recovered in place from Ossuary I at Seyr,
  the earliest securely excavated intact closure assigned to the horizon.
- **Function:** contained a simple mortuary curse within the burial niche.
- **Opening teacher intervention:** “The Seyric makers often laid one veil
  directly inside another. When nothing separates a pair, both may be lifted
  together.”
- **Learning:** introduces `release-paired-veils`.

Verified backward witness: one double-cut elimination.

### 2. Seyr Cairn Seal IV

- **Curator shorthand:** four-veil nesting.
- **Formal goal:** `¬¬¬¬⊤`.
- **Provenance:** the fourth slate closure catalogued from the outer cairn cache
  at Seyr; tool marks suggest it was cut during one workshop episode.
- **Function:** reinforced a cache curse through repeated nested closure.
- **Opening teacher intervention:** “There are two paired veils here. Either
  pair may be lifted first.”
- **Recognized-state teacher intervention:** after the first legal pair is
  lifted, “The lever beneath the lens records each state. You may draw it back
  to compare another route.” This is an affordance introduction, not a required
  detour.
- **Learning:** practices and assesses `release-paired-veils`; introduces
  `resolve-repeated-veils`.

Verified backward witness: two double-cut eliminations. Either legal order
reaches the same canonical intermediate state and may trigger the timeline
instruction once.

### 3. The Orra Gate Fragment

- **Curator shorthand:** forked field.
- **Formal goal:** `¬(¬⊤ ∧ ¬⊤)`.
- **Provenance:** a broken limestone lintel ward from the Orra Gate. The forked
  interior appears to be a later repair or accretion rather than the original
  carving.
- **Function:** confined a threshold curse while allowing one obstructing
  fragment to be cleared during licensed passage.
- **Opening teacher intervention:** “A dark field does not preserve every
  fragment drawn within it. You may clear away a complete fragment to expose a
  simpler form.”
- **Recognized-trap teacher intervention:** if one legal clearing removes the
  whole useful core and leaves an empty veil, “An empty veil is a familiar
  novice’s trap. Nothing remains inside it to work upon. Draw the lever back to
  before the clearing.” This intervention fires once and carries timeline
  recovery guidance.
- **Learning:** introduces `clear-dark-field`; retrieves
  `release-paired-veils`.

Verified backward witness: erasure, then double-cut elimination. A separate
legal demonstration trace must verify the empty-veil trap state.

### 4. Tel Vey Chamber Seal VIII

- **Curator shorthand:** supported-echo form.
- **Formal goal:** `¬(¬⊤ ∧ ¬¬⊤)`.
- **Provenance:** the eighth closure recorded in the Tel Vey storage chamber;
  its repeated inner fragment remains unusually crisp beneath mineral deposits.
- **Function:** reinforced a chamber curse by repeating an older surrounding
  form inside a deeper field.
- **Opening teacher intervention:** “The inner fragment is an exact echo of the
  older form outside it. Where the older form remains, the echo may be lifted.”
- **First stalled intervention:** “Compare the innermost fragment with the form
  in the surrounding field. The match must be exact.”
- **Learning:** introduces `lift-supported-echo`, practices `clear-dark-field`,
  and retrieves `release-paired-veils`.

Verified backward witness: deiteration, erasure, double-cut elimination.

### 5. The Auten Reliquary Closure

- **Curator shorthand:** single-ring ownership form.
- **Formal goal:** `∀P.P→P`.
- **Provenance:** a bronze-faced reliquary closure from Auten, preserving the
  first securely dated Seyric ring with a bound colored mark. Its discovery
  forced a revision of the horizon's chronology.
- **Function:** returned a marked condition through a veiled chamber while
  keeping both occurrences under one ring.
- **Opening teacher intervention:** “This colored mark belongs to the ring
  surrounding it. The veil changes where it appears, not which ring owns it.”
- **Completion teacher intervention:** “Good. The Seyric rings are ownership
  marks, not ornament. That distinction will matter among the Myratic finds.”
- **Learning:** introduces `trace-single-mark-ownership`, practices
  `lift-supported-echo` and `clear-dark-field`, and retrieves
  `release-paired-veils`.

Verified backward witness: deiteration, erasure, vacuous-bubble elimination,
double-cut elimination.

### 6. Seyric Field Seal S-27

- **Curator shorthand:** two-ring field form.
- **Formal goal:** `∀P,Q.(P∧Q)→P`.
- **Accession:** S-27.
- **Provenance:** a small repetitive tablet from Seyr workshop refuse, probably
  a routine exercise or production trial rather than a commissioned closure.
- **Function:** practiced separating two nested owners while retaining only the
  mark required by the seal.
- **First stalled intervention:** “Trace each color back to its own ring before
  removing anything.” There is no opening lecture.
- **Learning:** introduces `distinguish-nested-owners`, practices
  `trace-single-mark-ownership`, and assesses the first culture's core skills.
- **Progression:** elective.

Verified backward witness: deiteration, two erasures, two vacuous-bubble
eliminations, double-cut elimination.

### 7. The Uninscribed Votive of Myrat

- **Curator shorthand:** blank-hollow form.
- **Formal goal:** `∃P.P`.
- **Provenance:** an alabaster votive from the isolated Myrat complex. Wear and
  residue establish that its empty face is intentional and integral to the
  seal, not unfinished work or later damage.
- **Function:** required the maker or breaker to supply one complete pattern for
  its deliberate hollow.
- **Opening teacher intervention:** “The Myratic hollow is deliberate. It asks
  for an entire seal-pattern. Open the loupe and place the blank sheet within
  it.”
- **Completion teacher intervention:** “Precisely. To a Myratic seal, even an
  unwritten sheet is a complete pattern.”
- **Learning:** introduces `supply-complete-pattern` and retrieves
  `trace-single-mark-ownership`.

This gateway demonstrates only the Myratic tradition's first technique. The
full culture later develops compound and outer-dependent instantiation,
comprehension abstraction, vacuous and nested binders, ownership and shadowing,
quantifier movement and distribution, exhaustive proposition choice, and
impredicative proposition encodings. None of those later artifacts belong to
this pre-interface implementation slice.

Verified backward witness: one arity-zero comprehension instantiation with the
blank sheet.

## Catalog authority and validation

The generic title-only campaign model is replaced by culture authority. No
campaign alias or parallel campaign/culture concept remains. Catalog build must
reject:

- missing or cyclic culture and artifact dependencies;
- unreachable cultures or artifacts;
- open goals or witnesses that do not reach canonical blank;
- learning or mechanic claims contradicted by the witness;
- missing professional name, provenance, or teacher-intervention structure;
- invalid, open, or unreachable recognized proof states in teacher
  interventions;
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
