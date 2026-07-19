# Seyric Content Production Design

## Status and fixed decisions

This design governs production of the complete Seyric curriculum.

- Progression: evidence-shared spiral.
- Curriculum size: exactly 49 distinct skills and 186 distinct puzzles.
- Myratic gate: exactly 140 required puzzles in the final-transfer prerequisite closure.
- Optional content: exactly 46 puzzles outside that closure.
- Stage totals: 64 opening/structural puzzles, 51 connective/compositional puzzles, and 71 polarity/classical/reference puzzles.
- The existing seven puzzles remain the playable seed. Six belong to Seyric; `blank-witness` remains the initial Myratic puzzle.
- Proof physics, backward play, canonical-blank completion, artifact theorem semantics, and the passive guidance presentation do not change.
- The dedicated physics battery remains disabled and must not be run.

The total describes individual playable puzzles. Family headings, skill rows, internal decisions within a puzzle, and shared evidence labels do not count as additional puzzles.

## Outcome

The production system must turn the corrected Seyric roadmap into 186 individually authored, playable, verified artifacts while keeping the game operational after every accepted cohort. Parallel work must increase throughput without creating competing content authorities, shared-file conflicts, logically invalid witnesses, generic prose, or puzzles that claim to assess a skill they do not require.

The final curriculum must teach and test every selected skill through introduction, nearest-error contrast, at least two structurally varied applications, delayed retrieval, mixed use, and unfamiliar transfer. Requiredness is computed from the final transfer puzzle, never stored as a second hand-maintained flag.

## Scope boundaries

This phase includes:

- normalization of the 186-puzzle inventory;
- scalable content-fragment ownership and deterministic assembly;
- game-authorability and shortcut validation;
- formal feasibility spikes for risky proof families;
- authoring all semantic puzzles, solutions, curriculum records, artifact identities, provenance, and warranted guidance;
- independent logical, pedagogical, editorial, and runtime review;
- cohort integration through the final Myratic gate.

This phase does not:

- modify proof rules or expose kernel-only rules in the game;
- add a theorem picker, armed-reference mode, alternate completion condition, forward-proof mode, proof recording, or generic hints;
- use procedural filler to reach a count;
- create new visual assets or character art;
- treat a skill-family label as a puzzle;
- ship validation solutions, roadmap bookkeeping, authoring scripts, or review evidence in the desktop package.

## Authorities and representations

### Normalized roadmap

`content/roadmaps/seyric.json` is the build-only planning authority. Its schema is `content/schemas/seyric-roadmap.schema.json`. It contains:

- the 49 stable performance IDs;
- the 186 stable puzzle IDs;
- one primary skill and one primary evidence role for every puzzle;
- any additional skills for which the puzzle supplies shared evidence;
- stage and stable folio order;
- prerequisite puzzle IDs;
- evidence relationships for introduction, contrast, varied application, retrieval, mixed use, and transfer;
- the final-transfer puzzle ID.

It does not contain diagrams, solutions, lore, guidance prose, completion rules, proof-engine profiles, presentation parameters, or mutable workflow status. The production curriculum placement records must agree with it mechanically. The roadmap is excluded from runtime packaging.

The temporary HTML atlas is input evidence only. A derived HTML or graph report may be regenerated from `seyric.json`, but it cannot remain a planning authority.

### Portable production fragments

The existing concern boundaries remain authoritative, but singleton overlay arrays are replaced with disjoint strict JSON fragments:

```text
content/
  puzzles/<puzzle-id>.json
  placements/<puzzle-id>.json
  artifacts/<puzzle-id>.json
  guidance/<puzzle-id>.json              # only when interventions exist
  validation/<puzzle-id>.json            # build-only
  performances/<performance-id>.json
  cultures/curriculum/<culture-id>.json
  cultures/catalog/<culture-id>.json
  definitions/<definition-id>.json
  roadmaps/seyric.json                    # build-only
  manifest.json                           # generated
```

The fragment is the content authority. There is no second handwritten aggregate. `content/manifest.json` and `src/game/content/files.generated.ts` are deterministic generated indexes. The assembler rejects stale generated output. The runtime loader consumes only the fragmented manifest format; the displaced singleton-overlay format is migrated and removed without an adapter.

### Per-puzzle bundle

A complete authoring bundle is the conceptual set of files sharing one puzzle ID:

1. Core puzzle: only stable ID and semantic diagram.
2. Placement: prerequisites and learning evidence roles.
3. Artifact: professional identity and concise provenance.
4. Guidance: absent unless an introduction, exact recognized dead end, or authored completion response warrants it.
5. Validation: serialized intended solution, exact artifact dependencies, expected rule names, and demonstrations for every recognized state.

An author may use engine builders and serializers to construct the diagram and solution together, but the emitted strict JSON is authoritative. Executable puzzle definitions do not enter production source or runtime.

## Inventory normalization

The corrected atlas intends 186 puzzles but its raw labels are not internally enumerable to that number. Normalization happens before puzzle authorship:

1. Extract all 49 skill rows and every evidence cell.
2. Treat labels such as `contrast inside I-*` as decisions within the named introduction puzzle, not separate puzzle IDs.
3. Count a shared puzzle ID once, even when it supplies evidence for several skills.
4. Give every remaining puzzle exactly one primary skill and evidence role.
5. Reconcile the stage inventories to 64, 51, and 71 without adding filler or collapsing skills.
6. Compute the final-transfer prerequisite closure and require exactly 140 members.
7. Prove the other 46 have no outgoing prerequisite path into that closure.

If reconciliation would require removing a selected skill, merging distinct skills, changing the 186 total, or changing the 140/46 gate, normalization stops for a user decision. Mere duplicate-label and internal-label correction does not require another product decision.

## Production infrastructure gate

Mass authorship cannot begin until the content pipeline proves these capabilities:

### Disjoint assembly

`scripts/assemble-game-content.ts` discovers strict fragment directories, sorts by stable IDs and explicit folio order, writes the manifest and generated static import map atomically, and has a check mode that fails when generated files are stale. Authors never edit generated files.

The content loader accepts only the fragmented format and assembles the same immutable runtime catalog interface. Existing seven-puzzle content is migrated first, proving no behavioral drift.

### Player-authorable witnesses

Validation must reject any solution step unavailable through the game interface. The authority is a pure game-layer predicate shared with proof-move routing, not a duplicated string allowlist. It covers:

- erasure;
- closed single-term insertion;
- double-cut introduction and elimination;
- vacuous introduction and elimination;
- iteration and deiteration;
- conversion;
- named or loupe-authored comprehension instantiation;
- relation fold and unfold;
- fusion;
- theorem steps created by completed-record drops.

Kernel-only operations remain invalid content witnesses unless a later, separately approved game interaction exposes them.

### Definition integrity

Every reference in puzzles and definitions must resolve with exact arity. Definition boundaries must be well formed and spliceable, and definition dependencies must remain acyclic. Global definition visibility is explicitly audited for premature shortcuts; no curriculum claim may depend on a relation being hidden when the runtime exposes it globally.

### Artifact authority and shortcuts

Validation evidence stores `requiredArtifacts`: the exact completed records used by the intended witness. The validator derives, rather than stores, two broader sets:

- prerequisite closure: artifacts guaranteed before the puzzle unlocks;
- maximal reachable set: every other artifact the player could legally have completed before selecting the puzzle, including optional and independent siblings that do not depend on the candidate.

The intended witness replays with its exact dependencies. A separate shortcut audit exposes the maximal reachable set and rejects accidental one-step manifestation/dissolution, a duplicate theorem goal, or another bounded solution that bypasses the advertised performance.

### Curriculum audit

Rule-name coverage is not treated as mastery evidence. The roadmap and placements are audited directly for:

- one introduction for each performance before shared use;
- an explicit nearest-error contrast;
- at least two structurally varied applications;
- delayed retrieval after intervening work;
- mixed use after all participating skills have independent introductions;
- transfer evidence without stepwise guidance;
- remediation pointing to the nearest key prerequisite;
- exactly 140 required and 46 optional puzzles.

## Feasibility gate

Before bulk authoring, focused scratch experiments must prove representative puzzles for the proof families with the highest semantic or search risk:

1. contraction/iteration and both idempotence forms;
2. three-link implication composition;
3. binary case analysis;
4. one expansion and one factoring distribution direction;
5. one De Morgan direction whose statement is not merely a canonical duplicate;
6. excluded middle or content-bearing double-negation elimination;
7. Peirce-style feedback;
8. exact artifact selection plus manifestation;
9. exact artifact dissolution;
10. unfamiliar mixed transfer.

Each spike must demonstrate a closed zero-boundary goal, a complete player-authorable backward witness, readable rendered structure, a load-bearing advertised decision, and no known one-step artifact shortcut. Experimental files remain outside production until accepted. Failure is evidence: the theorem statement is revised within the same skill, or the family stops for a user decision. Proof physics is never changed to rescue a planned puzzle.

## Cohort structure

After the infrastructure and feasibility gates, production advances in dependency order. Cohorts contain roughly 9–15 puzzles, small enough to review completely and large enough for three parallel authors.

1. Opening normalization and required nested-owner foundation.
2. Polarity, insertion/erasure, and timeline branch use.
3. Content-bearing cuts, iteration/deiteration, and duplication.
4. Weakening, left/right projection, and left/right injection.
5. Idempotence plus honest exchange/reassociation recognition.
6. Structural retrieval, mixed use, and capstones.
7. Three- and four-link composition plus side premises.
8. Conjunction lifting, disjunction mapping, and binary cases.
9. Three-way cases, distribution expansion, and factoring.
10. Absorption plus connective retrieval and transfer.
11. Contraposition and mark-polarity retrieval.
12. Four distinct De Morgan directions.
13. Double-negation, excluded middle, reductio, and Peirce.
14. Exact artifact selection, manifestation, and dissolution.
15. Structural-variant retrieval and final unfamiliar transfer.
16. Optional remediation and challenge closure.

Normalization fixes the exact membership and count of each cohort. Cohort 16 may be interleaved earlier when its prerequisites are available, but those puzzles remain outside the final-transfer closure.

## Agent orchestration

One lead coordinator owns the roadmap, cohort contract, integration decisions, and final validation. With three worker slots, each cohort uses rotated passes:

### Authoring pass

Three authors receive disjoint puzzle IDs and frozen contracts containing:

- primary and shared skill evidence;
- prerequisites and exact artifact budget;
- allowed game moves;
- statement family and structural-variation constraint;
- guidance and copy constraints;
- required output paths and validation commands.

Authors write only to unique scratch directories. They return complete bundles and receipts, not patches to shared production files.

### Logic pass

Bundles rotate to an author who did not create them. The reviewer replays the witness, checks every step against game authorability, checks definition and artifact authority, tests advertised load-bearing choices, and searches for obvious or bounded shortcuts.

### Pedagogy and editorial pass

Bundles rotate again. This reviewer checks roadmap role, prerequisite load, variation from nearby puzzles, retrieval spacing, ambiguity, professional identity, provenance, passive guidance, completion copy, and absence of generic hints or placeholder lore.

### Integration pass

The lead resolves defects by evidence, not majority vote. Only complete accepted bundles enter the repository. The assembler regenerates indexes, then cohort, full-content, type, browser, build, and packaged-runtime checks run. Rejected bundles stay in scratch and return to their author with defects keyed by puzzle ID.

No worker commits, pushes, opens the desktop on the user's display, or edits another worker's bundle. All rendered and Electron checks use headless Chromium or Xvfb.

## Content quality contract

Every accepted puzzle must satisfy all of the following:

- It is semantically distinct from every existing puzzle start.
- Its complete solution is possible through current player-facing interactions.
- Its intended skill is necessary, not merely mentioned in metadata or incidentally present in a rule-name set.
- Its structure differs meaningfully from neighboring applications; cosmetic ID, layout, or proposition-name changes do not count as variation.
- Its prerequisite burden matches its curriculum position.
- Its artifact dependencies are exact and acyclic.
- It has no known shortcut under the maximal reachable completed-artifact set.
- Its diagram is readable at production lens sizes and in the dark proof palette.
- Any guidance is passive, easily ignored, paged by single paragraphs, and limited to introduction or an exact authored recovery state.
- Artifact identity and provenance are concise, internally consistent, and free of placeholder lore.
- Completion copy is concise and does not introduce scores, ranks, proof review, or replay controls.

Recognition performances use honest semantic variation. They never ask the player to perform a fake conjunction exchange or reassociation move when the underlying representation already treats order or grouping as nonsemantic.

## Failure handling

- A malformed or incomplete bundle never enters the production manifest.
- A failed witness is repaired at the statement or solution level; validation is not weakened.
- A kernel-valid but UI-inaccessible witness is rejected.
- A shortcut caused by an earlier artifact requires redesign of the candidate statement, prerequisites, or intended artifact decision. The validator never hides artifacts that runtime could expose.
- A repeated pedagogy defect returns to the skill graph: split an overloaded performance, add a missing prerequisite, or revise evidence placement. It is not patched with more teacher prose.
- A feasibility failure that threatens a selected skill, total count, or gate stops for user direction.
- A cohort is not partially accepted. Previously accepted cohorts remain playable while defects are corrected in scratch.

## Validation and completion evidence

### Per bundle

- schema validation;
- semantic diagram construction and exact-definition checks;
- game-authorability validation;
- intended witness replay to canonical blank;
- JSON serialization round trip;
- exact artifact dependency validation;
- maximal-reachable artifact shortcut audit;
- canonical-start duplicate check;
- logic review receipt;
- pedagogy/editorial review receipt;
- rendered readability check for representative complex diagrams.

### Per cohort

- exact cohort membership and prerequisite satisfaction;
- deterministic assembly with no stale generated files;
- `npm run content:validate`;
- focused game/controller/save/folio tests;
- TypeScript check;
- authoritative browser tests under headless Chromium;
- desktop build and isolated Xvfb startup;
- a playable archive-to-puzzle-to-save restoration smoke.

### Final curriculum

The final receipt must report:

```text
skills: 49
puzzles: 186
required final-transfer closure: 140
optional outside closure: 46
opening/structural: 64
connective/compositional: 51
polarity/classical/reference: 71
puzzle bundles complete: 186/186
solutions replayed: 186/186
logic reviews accepted: 186/186
pedagogy/editorial reviews accepted: 186/186
duplicate canonical starts: 0
UI-inaccessible witness steps: 0
missing evidence roles: 0
optional paths into required closure: 0
packaged validation sidecars or roadmap files: 0
```

The final packaged smoke must prove archive ordering, unlocks, required/optional status, completed-record theorem use, timeline rewind, completion, Myratic gating, save persistence, and startup restoration. The work is not complete merely because 186 JSON files exist.

## Delivery sequence

The implementation is divided into separately reviewable projects:

1. Normalize and validate the canonical roadmap.
2. Rebuild content fragments and deterministic assembly.
3. Add game-authorability, definition-integrity, artifact-shortcut, and curriculum validators.
4. Complete and approve feasibility spikes.
5. Produce cohorts 1–16 through the author/reviewer/integrator loop.
6. Run the final curriculum and packaged-runtime acceptance pass.

No broad content cohort starts before projects 1–4 pass. This front-loads the defects that would otherwise multiply across hundreds of files.
