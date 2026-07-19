# Seyric Content Production Design

## Status and fixed decisions

This design governs production of the complete Seyric curriculum.

- Progression: evidence-shared spiral.
- Approved baseline: 49 distinct skills and 186 distinct puzzles.
- Baseline Myratic closure: 140 required puzzles leading to the final transfer.
- Baseline optional content: 46 practice, remediation, or challenge puzzles outside that closure.
- Baseline stage totals: 64 opening/structural puzzles, 51 connective/compositional puzzles, and 71 polarity/classical/reference puzzles.
- Warranted expansion is automatic. The coordinator adds puzzles when logical feasibility, evidence density, structural variation, remediation, or transfer quality warrants them, without requesting permission.
- The existing seven puzzles remain the playable seed. Six belong to Seyric; `blank-witness` remains the initial Myratic puzzle.
- Proof physics, backward play, canonical-blank completion, artifact theorem semantics, and the passive guidance presentation do not change.
- Every existing user-facing logical mechanic on `main` is ported into the game. Every move required in the pure propositional layer has a user interaction, whether inherited from `main` or added during engine integration.
- The dedicated physics battery remains disabled and must not be run.

The baseline total describes individual playable puzzles. Family headings, skill rows, internal decisions within a puzzle, and shared evidence labels do not count as additional puzzles. Added puzzles receive new stable identities and the same complete evidence and validation treatment; they are not hidden inside existing slots.

## Outcome

The production system must turn the corrected 186-puzzle Seyric baseline, plus every warranted addition, into individually authored, playable, verified artifacts while keeping the game operational after every accepted cohort. Parallel work must increase throughput without creating competing content authorities, shared-file conflicts, logically invalid witnesses, generic prose, or puzzles that claim to assess a skill they do not require.

The final curriculum must teach and test every selected skill through introduction, nearest-error contrast, at least two structurally varied applications, delayed retrieval, mixed use, and unfamiliar transfer. Requiredness is computed from the final transfer puzzle, never stored as a second hand-maintained flag.

## Scope boundaries

This phase includes:

- normalization of the 186-puzzle inventory;
- automatic addition of puzzles warranted by the curriculum or formal evidence;
- scalable content-fragment ownership and deterministic assembly;
- complete porting of main user-facing logical mechanics and centrally validated pure-propositional interaction coverage;
- logical witness and shortcut validation;
- formal feasibility spikes for risky proof families;
- authoring all semantic puzzles, solutions, curriculum records, artifact identities, provenance, and warranted guidance;
- independent logical, pedagogical, editorial, and runtime review;
- cohort integration through the final Myratic gate.

This phase does not:

- modify proof physics to rescue a planned puzzle;
- use the game worktree's current interaction subset to constrain puzzle content;
- ask for approval before adding warranted puzzle content;
- add a theorem picker, armed-reference mode, alternate completion condition, forward-proof mode, proof recording, or generic hints;
- use procedural filler to reach a count;
- create new visual assets or character art;
- treat a skill-family label as a puzzle;
- ship validation solutions, roadmap bookkeeping, authoring scripts, or review evidence in the desktop package.

## Authorities and representations

### Normalized roadmap

`content/roadmaps/seyric.json` is the build-only planning authority. Its schema is `content/schemas/seyric-roadmap.schema.json`. It contains:

- the 49 stable performance IDs;
- all 186 baseline puzzle IDs and every warranted additional puzzle ID;
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
5. Reconcile the baseline stage inventories to 64, 51, and 71 without adding filler or collapsing skills.
6. Compute the baseline final-transfer prerequisite closure and recover its 140 intended members.
7. Recover the baseline 46 optional puzzles and prove they have no outgoing prerequisite path into that closure.
8. Add new stable puzzle records whenever the normalized evidence graph shows that another isolated example, contrast, variation, retrieval, remediation, or transfer is warranted.

The 186 baseline puzzles cannot be silently removed or collapsed. Removing a selected skill still requires a user decision. Increasing the puzzle count does not: additions are made whenever warranted, and required/optional totals are recomputed from the resulting final-transfer graph. Mere duplicate-label and internal-label correction also does not require another product decision.

## Production infrastructure gate

Mass authorship cannot begin until the content pipeline proves these capabilities:

### Disjoint assembly

`scripts/assemble-game-content.ts` discovers strict fragment directories, sorts by stable IDs and explicit folio order, writes the manifest and generated static import map atomically, and has a check mode that fails when generated files are stale. Authors never edit generated files.

The content loader accepts only the fragmented format and assembles the same immutable runtime catalog interface. Existing seven-puzzle content is migrated first, proving no behavioral drift.

### Interaction parity and propositional completeness

Interaction availability is an engine-integration responsibility, not a content-authoring constraint. Before content agents are dispatched, the engine-integration owner:

1. inventories every user-facing logical mechanic and interaction already available on `main`;
2. ports each one into the game while preserving its logical behavior;
3. enumerates the complete pure propositional move vocabulary, including later moves exposed by normalized curriculum and feasibility proofs;
4. implements a game interaction for every missing required move;
5. proves the resulting interaction coverage centrally through direct route and rendered-browser tests.

Content authors and reviewers are not given an interaction allowlist and do not inspect the game controller to decide what content is permitted. Content validation replays witnesses against the proof calculus. If a valid propositional witness reveals a missing game interaction during central integration, the engine owner adds that interaction; the puzzle is not weakened or rejected to match the temporary port state.

The port copies the mechanics into game ownership; it does not create a runtime dependency on `main`, merge the game into `main`, or leave main as a second game-mechanics authority.

The artifact-record theorem interaction remains game-owned, and the circular construction editor remains the game presentation of construction. These presentation choices do not narrow the available logical curriculum.

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
- preservation of all 186 baseline puzzle roles and all warranted additions;
- a required/optional split derived from the actual final-transfer closure, with the original 140/46 split retained as baseline evidence rather than a ceiling.

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

Each spike must demonstrate a closed zero-boundary goal, a complete verified backward witness, readable rendered structure, a load-bearing advertised decision, and no known one-step artifact shortcut. Experimental files remain outside production until accepted. Failure is evidence: the theorem statement is revised, the family receives additional puzzles when more isolation or practice is warranted, or removal of a selected skill stops for a user decision. Proof physics is never changed to rescue a planned puzzle.

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

Normalization fixes the baseline membership of each cohort. Warranted additions are assigned to the earliest cohort whose prerequisites and evidence role they satisfy, or to a new expansion cohort when that keeps review boundaries clearer. Baseline cohort 16 may be interleaved earlier when its prerequisites are available, but its optional puzzles remain outside the final-transfer closure.

## Agent orchestration

One lead coordinator owns the roadmap, cohort contract, integration decisions, and final validation. With three worker slots, each cohort uses rotated passes:

### Authoring pass

Three authors receive disjoint puzzle IDs and frozen contracts containing:

- primary and shared skill evidence;
- prerequisites and exact artifact budget;
- the logical skill and theorem family, without reference to current interaction-port status;
- statement family and structural-variation constraint;
- guidance and copy constraints;
- required output paths and validation commands.

Authors write only to unique scratch directories. They return complete bundles and receipts, not patches to shared production files.

### Logic pass

Bundles rotate to an author who did not create them. The reviewer replays the witness against the proof calculus, checks definition and artifact authority, tests advertised load-bearing choices, and searches for obvious or bounded shortcuts. The reviewer does not inspect or reason about user-interface coverage.

### Pedagogy and editorial pass

Bundles rotate again. This reviewer checks roadmap role, prerequisite load, variation from nearby puzzles, retrieval spacing, ambiguity, professional identity, provenance, passive guidance, completion copy, and absence of generic hints or placeholder lore.

### Integration pass

The lead resolves defects by evidence, not majority vote. Only complete accepted bundles enter the repository. The assembler regenerates indexes, then cohort, full-content, type, browser, build, and packaged-runtime checks run. Rejected bundles stay in scratch and return to their author with defects keyed by puzzle ID.

No worker commits, pushes, opens the desktop on the user's display, or edits another worker's bundle. All rendered and Electron checks use headless Chromium or Xvfb.

## Content quality contract

Every accepted puzzle must satisfy all of the following:

- It is semantically distinct from every existing puzzle start.
- Its complete solution is valid under the proof calculus and uses the intended theorem and artifact authority.
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
- A missing interaction for a valid pure-propositional move creates an engine-integration task and is resolved centrally before the cohort becomes playable; it does not invalidate or narrow the puzzle.
- A shortcut caused by an earlier artifact requires redesign of the candidate statement, prerequisites, or intended artifact decision. The validator never hides artifacts that runtime could expose.
- A repeated pedagogy defect returns to the skill graph: split an overloaded performance, add a missing prerequisite, or revise evidence placement. It is not patched with more teacher prose.
- A feasibility failure is handled by revising the statement or adding warranted isolation and practice puzzles. Only removing a selected skill or changing proof physics requires user direction.
- A cohort is not partially accepted. Previously accepted cohorts remain playable while defects are corrected in scratch.

## Validation and completion evidence

### Per bundle

- schema validation;
- semantic diagram construction and exact-definition checks;
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
- central proof that every main logical interaction is present in the game and no required pure-propositional move lacks a game interaction;
- `npm run content:validate`;
- focused game/controller/save/folio tests;
- TypeScript check;
- authoritative browser tests under headless Chromium;
- desktop build and isolated Xvfb startup;
- a playable archive-to-puzzle-to-save restoration smoke.

### Final curriculum

The final receipt must report:

```text
baseline skills retained: 49/49
baseline puzzle IDs retained: 186/186
additional warranted puzzle IDs: actual count
total puzzles: computed actual count
baseline required evidence retained: 140/140
actual required final-transfer closure: computed actual count
baseline optional evidence retained: 46/46
actual optional outside closure: computed actual count
baseline opening/structural retained: 64/64
baseline connective/compositional retained: 51/51
baseline polarity/classical/reference retained: 71/71
puzzle bundles complete: actual total / actual total
solutions replayed: actual total / actual total
logic reviews accepted: actual total / actual total
pedagogy/editorial reviews accepted: actual total / actual total
duplicate canonical starts: 0
missing evidence roles: 0
optional paths into required closure: 0
main interactions missing from game: 0
required pure-propositional interactions missing: 0
packaged validation sidecars or roadmap files: 0
```

The final packaged smoke must prove archive ordering, unlocks, required/optional status, completed-record theorem use, timeline rewind, completion, Myratic gating, save persistence, startup restoration, and the integrated interaction vocabulary. The work is not complete merely because the 186 baseline JSON bundles and any additions exist.

## Delivery sequence

The implementation is divided into separately reviewable projects:

1. Normalize and validate the canonical roadmap.
2. Rebuild content fragments and deterministic assembly.
3. Port every existing user-facing logical mechanic from `main` and complete the pure-propositional interaction surface under central engine ownership.
4. Add definition-integrity, artifact-shortcut, and curriculum validators.
5. Complete and approve feasibility spikes, adding puzzles whenever the evidence warrants them.
6. Produce cohorts 1–16 and any warranted expansion cohorts through the author/reviewer/integrator loop.
7. Run the final curriculum and packaged-runtime acceptance pass.

No broad content cohort starts before projects 1–5 pass. This gives authors a stable logical curriculum while keeping interaction-port reasoning entirely out of their work.
