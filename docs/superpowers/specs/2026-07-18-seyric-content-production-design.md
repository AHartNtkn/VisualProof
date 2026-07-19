# Seyric Puzzle Content Production Design

## Scope

This phase creates Seyric puzzle content. It owns:

- the normalized puzzle inventory;
- curriculum performances, placements, prerequisites, and evidence roles;
- semantic puzzle diagrams;
- verified backward solutions;
- artifact names and provenance;
- optional authored guidance and completion responses;
- dependency-ordered authoring batches;
- logical, pedagogical, and editorial review;
- integration through the existing layered content format;
- content validation.

It does not redesign any adjacent system.

## Fixed direction

- Progression uses the evidence-shared spiral.
- The approved baseline contains 49 skills and 186 individual puzzles.
- The baseline final-transfer closure contains 140 required puzzles.
- The baseline contains 46 optional practice, remediation, or challenge puzzles.
- Baseline stage totals are 64 opening/structural, 51 connective/compositional, and 71 polarity/classical/reference puzzles.
- The six existing Seyric puzzles remain in their current opening positions.
- `blank-witness` remains the first Myratic puzzle.
- The final required Seyric transfer puzzle is the Myratic unlock dependency.
- When another puzzle is warranted by logical clarity, skill isolation, variation, retrieval, remediation, or transfer quality, it is added without requesting permission. The baseline is not a ceiling.

Family headings, skill rows, internal decisions within a puzzle, and shared evidence labels are not puzzles. Every puzzle has one stable identity and one playable semantic statement.

## Existing content contract

All production content uses the existing strict JSON layers.

### Core puzzle

`content/puzzles/<puzzle-id>.json` contains only:

```text
id
diagram
```

### Curriculum

`content/curriculum/core.json` owns:

- performance definitions;
- performance prerequisites and knowledge points;
- culture order and puzzle order;
- puzzle prerequisites;
- introduction, practice, retrieval, and assessment roles.

### Catalog

`content/catalog/cursebreaker.json` owns:

- professional artifact names;
- curator shorthand and accession where warranted;
- provenance summaries and functions;
- findspots and attributions where warranted.

### Guidance

`content/guidance/cursebreaker.json` owns optional authored interventions. A puzzle receives guidance only when the content warrants an introduction, an exact recognized recovery state, or a concise completion response.

### Validation evidence

`content/validation/<puzzle-id>.json` owns:

- the complete backward solution;
- completed artifacts used by that solution;
- the exact set of rules used;
- demonstrations for every authored recognized state.

Validation evidence remains build-only.

### Definitions and registration

Shared logical definitions use `content/definitions/*.json`. The integrator updates `content/manifest.json` and the existing static content registration whenever accepted files are added. These are routine content-registration edits, not a new content path.

## Inventory normalization

The temporary atlas records the intended curriculum but its raw labels do not enumerate consistently. Before authoring new puzzles, the coordinator creates one normalized inventory with these rules:

1. Preserve all 49 approved skill rows.
2. Preserve all six existing Seyric puzzle IDs and their positions.
3. Treat phrases such as `contrast inside I-*` as internal decisions within that puzzle, not separate IDs.
4. Count a shared puzzle ID once even when it supplies evidence for several skills.
5. Assign every puzzle one primary skill, one primary evidence role, one stage, and one stable folio position.
6. Record additional skills for which a shared puzzle supplies evidence.
7. Reconcile the approved baseline to 64, 51, and 71 puzzles by stage and 186 overall.
8. Recover the baseline 140-puzzle final-transfer closure and 46 puzzles outside it.
9. Add any further puzzles warranted during normalization as new stable records rather than hiding them inside baseline records.

The normalized inventory is the coordinator's batch authority. The rendered atlas becomes a derived review view, not a second list.

## Skill evidence contract

Each skill must receive enough distinct puzzle evidence to establish mastery rather than familiarity:

- an introduction that isolates the new decision;
- a nearest-error contrast;
- at least two structurally varied applications;
- delayed retrieval after intervening material;
- mixed use after all participating skills have been introduced independently;
- unfamiliar transfer without stepwise solution guidance;
- remediation or additional practice where the error profile warrants it.

A shared puzzle may satisfy evidence for several skills only when each skill is independently necessary to its solution. Cosmetic proposition renaming, node-ID changes, or layout changes do not count as structural variation.

Recognition skills remain honest about the semantic representation. They use contrasting or unfamiliar structures; they do not invent a transformation when two presentations are already semantically identical.

## Puzzle bundle

An author receives a frozen puzzle brief containing:

- puzzle ID and folio position;
- primary skill and evidence role;
- any shared evidence roles;
- prerequisites;
- required or optional graph role;
- intended theorem family;
- allowed completed-artifact dependencies;
- structural-variation requirement;
- nearby puzzles that must not be duplicated;
- copy and guidance constraints.

The author returns one complete scratch bundle:

1. Core puzzle JSON.
2. Curriculum placement fragment.
3. Artifact record fragment.
4. Guidance fragment or an explicit statement that none is warranted.
5. Validation sidecar with a complete solution.
6. A short author receipt explaining why the advertised skill is necessary and how the puzzle differs from its neighbors.

Authors use the repository's diagram and proof serializers when constructing content. The emitted JSON is the durable content; executable authoring experiments remain scratch work.

## Feasibility pass

Before bulk production of a difficult family, one representative puzzle is authored and reviewed in scratch. The initial feasibility set covers:

- contraction and idempotence;
- three-link composition;
- binary case analysis;
- distribution expansion and factoring;
- a nontrivial De Morgan direction;
- excluded middle or content-bearing double negation;
- Peirce-style feedback;
- exact artifact selection and manifestation;
- exact artifact dissolution;
- unfamiliar mixed transfer.

Each representative must have:

- a closed semantic statement;
- a complete backward solution reaching blank;
- a readable structure;
- a load-bearing advertised decision;
- no obvious artifact shortcut;
- a clear distinction from neighboring puzzle statements.

Failed representatives are revised or expanded into additional isolation puzzles. They are not copied into production until accepted.

## Production cohorts

Content proceeds in dependency order through these baseline cohorts:

1. Opening normalization and required nested-owner foundation.
2. Polarity, insertion/erasure, and timeline branch reasoning.
3. Content-bearing cuts, iteration/deiteration, and duplication.
4. Weakening, left/right projection, and left/right injection.
5. Idempotence and structural recognition.
6. Structural retrieval, mixed use, and capstones.
7. Three- and four-link composition plus side premises.
8. Conjunction lifting, disjunction mapping, and binary cases.
9. Three-way cases, distribution expansion, and factoring.
10. Absorption plus connective retrieval and transfer.
11. Contraposition and polarity retrieval.
12. Four distinct De Morgan directions.
13. Double negation, excluded middle, reductio, and Peirce.
14. Exact artifact selection, manifestation, and dissolution.
15. Structural-variant retrieval and final unfamiliar transfer.
16. Optional remediation and challenge closure.

Each cohort contains roughly 9–15 puzzles. Warranted additions join the earliest suitable cohort or form a focused expansion cohort.

## Parallel orchestration

The coordinator retains sole ownership of the normalized inventory and repository integration. With three worker slots, every cohort uses three passes.

### Authoring pass

Three authors receive disjoint puzzle IDs and write complete bundles to disjoint scratch directories. They do not edit shared production arrays or registration files.

### Logic review pass

Bundles rotate to reviewers who did not author them. Logic review checks:

- semantic well-formedness;
- complete replay to blank;
- exact artifact authority;
- prerequisite compatibility;
- necessity of the advertised proof decision;
- duplication and obvious shortcut risk;
- correctness of recognized-state demonstrations.

### Pedagogy and editorial pass

Bundles rotate again. This review checks:

- correct evidence role and curriculum position;
- meaningful variation from nearby puzzles;
- prerequisite load;
- retrieval and transfer spacing;
- professional artifact identity;
- concise, internally consistent provenance;
- absence of placeholder lore;
- restraint and specificity of guidance and completion copy.

### Integration pass

The coordinator admits only complete accepted bundles. The coordinator:

1. writes the core puzzle and validation files;
2. merges placement, artifact, and guidance fragments into their existing layers;
3. updates puzzle ordering and prerequisites;
4. updates the manifest and static registration;
5. runs focused validation;
6. returns any defect to the responsible author by puzzle ID.

Partially accepted bundles never enter production content.

## Acceptance standard

Every accepted puzzle must satisfy all of the following:

- The core diagram is strict, closed, and semantically distinct from existing starts.
- The complete validation solution replays to canonical blank.
- Every named prerequisite, performance, definition, and artifact exists.
- Artifact use is available from the puzzle's prerequisite closure.
- The advertised skill is necessary to the solution.
- The statement is not a cosmetic variant of another puzzle.
- Its complexity fits its curriculum position.
- Its evidence role is recorded accurately.
- Its artifact identity and provenance are finished copy.
- Guidance is omitted unless it has a specific authored purpose.
- Every recognized state has an exact replayable demonstration.

A puzzle that fails any item returns to scratch for correction. Validation expectations are not weakened to admit it.

## Validation cadence

### Per puzzle

- Parse every JSON layer.
- Construct the semantic diagram.
- Replay the complete solution to blank.
- Verify expected rules and artifact dependencies.
- Replay every recognized-state demonstration.
- Compare the canonical start against accepted puzzles.
- Complete logic and pedagogy/editorial review receipts.

### Per cohort

- Verify cohort IDs, order, and prerequisites against the normalized inventory.
- Run `npm run content:validate`.
- Run focused catalog, progress, save, guidance, and artifact tests.
- Run the type check and production content build.
- Confirm that the expanded catalog loads with the accepted cohort.

### Final receipt

The final report records:

```text
baseline skills retained: 49/49
baseline puzzle IDs retained: 186/186
additional warranted puzzles: actual count
total accepted puzzles: actual count
actual required final-transfer closure: actual count
actual optional puzzles outside closure: actual count
complete puzzle bundles: total/total
solutions replayed to blank: total/total
logic reviews accepted: total/total
pedagogy/editorial reviews accepted: total/total
duplicate canonical starts: 0
missing curriculum evidence roles: 0
invalid prerequisites or artifact dependencies: 0
unfinished artifact or guidance copy: 0
```

Completion means every accepted puzzle has complete content and validation evidence. A count without complete, reviewed bundles is not completion.

## Delivery order

1. Normalize the 186-puzzle baseline inventory.
2. Author and approve the representative feasibility set.
3. Produce dependency-ordered cohorts through the three-pass review loop.
4. Integrate and validate each complete cohort.
5. Add warranted expansion puzzles whenever evidence shows they are needed.
6. Complete the final content receipt.
