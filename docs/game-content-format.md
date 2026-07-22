# Cursebreaker game content format

`content/manifest.json` is the sole production content entry point. It is strict
JSON with `format: "cursebreaker-content"` and `version: 3`. The manifest names
the ordered puzzle and logical-definition files, one progression, catalog, and
guidance file, and one build-only coverage file for each catalog culture:

```json
{
  "format": "cursebreaker-content",
  "version": 3,
  "puzzles": ["puzzles/example.json"],
  "definitions": [],
  "progression": "progression/core.json",
  "coverage": {
    "seyric-horizon": "coverage/seyric.json",
    "myratic-tradition": "coverage/myratic.json"
  },
  "catalog": "catalog/cursebreaker.json",
  "guidance": "guidance/cursebreaker.json"
}
```

Every content file is strict JSON validated against `content/schemas/`; unknown
fields are errors. Runtime loading validates the manifest shape and imports the
runtime layers. Coverage is build-only: runtime loading validates the culture-to-
path map but does not import those payloads. Content validation loads every layer,
including coverage and per-puzzle validation sidecars. Desktop packaging excludes
both build-only coverage and validation sidecars.

## Layer ownership

### Puzzle core and definitions

Each `content/puzzles/<puzzle-id>.json` file contains exactly a stable semantic ID
and starting diagram:

```json
{
  "id": "example",
  "diagram": {
    "root": "r0",
    "regions": { "r0": { "kind": "sheet" } },
    "nodes": {},
    "wires": {}
  }
}
```

The core does not contain placement, lore, guidance, coverage claims, or a
solution. Backward play and completion at canonical blank are engine invariants,
not configurable content. `content/definitions/*.json` contains shared logical
definitions referenced by diagrams; each definition owns its ID, diagram, and
boundary.

### Progression

`content/progression/core.json` is the only owner of runtime ordering and gates.
Its `cultures` array owns culture order, cross-culture unlock requirements, each
culture gateway, and folio puzzle order. Its `placements` array gives every
puzzle exactly one record with `puzzle` and `prerequisites`.

Culture ownership follows logical structure. A puzzle with one outer goal cut,
a leading chain of arity-zero proposition binders, and a quantifier-free matrix
of cuts and bound proposition occurrences belongs to Seyric. Myratic begins when
binder scope, placement, or transformation is itself part of the proof problem.
Validation enforces this boundary in both directions.

The Seyric puzzles that must be completed before the first Myratic puzzle unlocks
are derived solely from the Myratic culture-unlock conditions and their transitive
prerequisite closure. Every other Seyric puzzle is practice outside that mandatory
path. There is no separate required-or-optional placement value.

### Build-only coverage

Each manifest-owned `content/coverage/<culture>.json` file is authoring and audit
evidence for exactly one culture. `obligations` records the approved onboarding,
isolated, carried-interaction, or mixed distinctions, their family, and stopping
rules. `puzzles` maps every puzzle owned by that culture to claimed obligations,
the visible situation, the narrower hypothesis or simpler strategy it defeats,
and its experiential neighbors. A Seyric row may additionally name an
`immediateComplementPattern` when the start deliberately exposes an exact
graphical sibling occurrence matching the complete contents of a direct cut;
these pattern names are unique review classifications, not runtime mechanics.

Coverage describes and validates records that have already been authored. It
cannot generate a puzzle, retain or replace one, place one on the mandatory path,
order it, unlock it, gate it, or affect runtime behavior or logical identity.
Coverage completeness is a build-time validation requirement; coverage metadata
is never a source of runtime records. Puzzle count is never a target, quota,
floor, cap, batch size, preservation constraint, or measure of content quality.

### Catalog

`content/catalog/cursebreaker.json` owns culture presentation and the finished
artifact record for each puzzle. Culture entries contain names, chronology,
lineage, isolation, and sealing vocabulary. Artifact entries contain the puzzle
reference, professional naming, and concise provenance. Catalog prose cannot
create logical identity, progression authority, or a reason to retain a
redundant puzzle.

### Guidance

`content/guidance/cursebreaker.json` owns optional authored interventions for a
puzzle. An intervention has its own ID, an `opening`, `completion`, or exact
`recognizedUnwinnable` trigger, repeat behavior, and one or more single-paragraph
pages. Recognized-unwinnable guidance also names the exact semantic state and
recovers through the timeline.

A puzzle may have no guidance entry. Guidance can explain a visible interaction,
but it cannot supply missing puzzle value, define a solution, create a curriculum
role, or gate progression.

### Validation sidecars

Each `content/validation/<puzzle-id>.json` contains:

- `puzzle`: the matching puzzle ID;
- `solution`: one complete backward witness;
- `availableArtifacts`: completed artifacts available to that witness;
- `expectedRules`: the rules observed in that witness; and
- `recognizedStates`: replayable demonstrations for exact recognized guidance
  states.

The witness must replay to canonical blank and every recognized-state
demonstration must reach its declared semantic state. This proves feasibility
only. The stored witness is not intended, unique, shortest, or mandatory, and
`expectedRules` does not constrain other valid solutions.

## Logical fingerprints

The catalog computes a puzzle fingerprint from the exact JSON serialization of
the canonical starting diagram after replacing every referenced definition name
with that definition's recursively canonical semantic form. Definition IDs and
incidental diagram object IDs therefore do not determine logical identity, while
the referenced logical semantics do.

Puzzle ID is stored separately. Progression, coverage, catalog names and
provenance, guidance, validation evidence, and presentation do not enter a
puzzle's logical fingerprint. Save decoding compares stored fingerprints with
the current catalog so logical drift is rejected while presentation-only edits
remain compatible.

## Culture syntax and redundancy authority

A Seyric authored start has exactly one ordinary outer goal cut. Inside it is an
optional uninterrupted prefix of arity-zero bubbles followed by a matrix made
only of atom marks and ordinary cuts. The matrix contains no bubbles or wires,
and every atom is owned by a bubble in that outer prefix. The prefix supplies
global proposition ownership: identifying which global ring owns an occurrence
and removing the vacuous prefix during terminal cleanup are Seyric mechanics.
A validation witness may remove only that contiguous prefix, deepest first,
after the propositional work; only trailing double-cut cleanup may follow.
Nontrivial local binder placement, scope, introduction, or transformation belongs
to Myratic.

This authoring boundary does not restrict the proof moves available to the
player. It constrains production starts and their feasibility witnesses so the
Seyric collection remains propositionally focused.

Content validation applies three distinct redundancy checks to Seyric starts:

- the existing canonical logical fingerprint rejects exact duplicates;
- a structural matrix fingerprint rejects starts that differ only by the order
  or names of the harmless global prefix while preserving binder cardinality and
  cut topology; and
- exact graphical sibling-occurrence starts require a unique approved
  `immediateComplementPattern`, making each retained shortcut's experiential
  purpose explicit. The audit uses the same extracted subgraph, canonical
  boundary form, and binder attachments as playable occurrence matching. It
  compares every nonempty sibling subset with each direct cut's complete
  contents and never normalizes through De Morgan, double-negation,
  distribution, or another proof transformation.

These checks do not impose an intended solution and do not replace direct
content review.

## Complete authoring bundle

A puzzle is ready for integration only as a complete bundle:

1. one strict core puzzle file;
2. one progression placement and one culture folio entry;
3. one catalog artifact entry;
4. one coverage mapping to existing approved obligations;
5. one validation sidecar with a replayable complete witness and any recognized-
   state demonstrations;
6. a guidance entry only when a specific authored intervention is warranted;
7. the puzzle path in manifest order; Vite derives build-time availability
   automatically from the approved runtime content directories.

If the bundle introduces a culture or logical definition, it also includes the
matching progression, catalog, definition, and manifest records. The manifest
alone registers and orders content; discovery makes files available but does not
register them. Partial bundles do not enter production. Deleted puzzles are
removed from every layer and import surface; aliases, tombstones, compatibility
maps, and fallback content paths are not authoring mechanisms.

Run `npm run content:validate` after assembling a bundle. It schema-validates
every layer, checks graph and cross-reference integrity, validates culture-owned
coverage and the derived Myratic unlock path, enforces the Seyric syntax and
redundancy authorities, verifies artifact availability, replays every witness to
canonical blank, and replays recognized-state demonstrations.
