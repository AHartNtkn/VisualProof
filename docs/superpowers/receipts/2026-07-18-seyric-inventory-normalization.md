# Seyric Inventory Normalization Receipt

## Authority and scope

This receipt is derived from `content/roadmaps/seyric.json`, the structural,
connective, and classical normalization reports, and
`tests/game/seyric-roadmap.test.ts`. The roadmap remains the sole inventory
authority; this document records review evidence only. This normalization authored
inventory metadata, not production puzzle diagrams, solutions, catalog copy, or
guidance.

## Emitted baseline

| Measure | Emitted result |
| --- | ---: |
| Skills | 49 |
| Structural skills / puzzles | 23 / 64 |
| Connective skills / puzzles | 13 / 51 |
| Classical/reference skills / puzzles | 13 / 71 |
| Total baseline puzzles | 186 |
| Required final-transfer closure | 140 |
| Optional complement | 46 |
| Duplicate puzzle IDs | 0 |
| Unclassified source labels | 0 |
| Missing mastery-evidence categories | 0 |
| Skill or puzzle graph cycles | 0 |

Folio positions are continuous and unique from 0 through 185. All skill,
prerequisite, and evidence references resolve.

## Count reconciliation

- Structural source rows supplied 63 distinct puzzle labels. The baseline adds one
  warranted record, `mixed-structural-synthesis`, to reach 64. It is a bounded
  optional challenge supporting weakening, projection, and both injection choices;
  its four evidence relationships are `challenge`, not mastery-spine `mixed`
  evidence.
- Connective rows emit 51 records after shared IDs are stored once and all 13
  `contrast inside I-*` labels are classified as decisions inside their owning
  introductions.
- Classical/reference rows contain 73 unique raw labels. `SEY-CTR-C01` is an
  internal decision in `SEY-CTR-V01`, and `SEY-DNE-C01` is an internal decision in
  `SEY-DNE-V01`, producing the accepted 71 records without dropping either source
  label.

## Final-transfer closure

The final transfer is `SEY-XFER-T01` at folio position 172. It depends on
`SEY-XFER-V01`, `SEY-XFER-V02`, `SEY-XFER-V03`, `SEY-XFER-V04`, and
`SEY-XFER-R01`. Its prerequisite closure, including itself, contains exactly 140
records:

| Stage | Required | Optional |
| --- | ---: | ---: |
| Structural | 51 | 13 |
| Connective | 31 | 20 |
| Classical/reference | 58 | 13 |
| **Total** | **140** | **46** |

These counts are derived only from prerequisite reachability; there is no separate
requiredness flag. `T3` is genuinely required because `SEY-XFER-I01` depends on it
and is in the final-transfer closure. `mixed-structural-synthesis` is genuinely
optional because no required record depends on it. Every record in the 46-item
complement has only remediation or challenge evidence.

## Internal atlas-label ownership

Structural normalization has no internal labels. The complete set of 15 mappings
is:

| Internal source label | Owning puzzle |
| --- | --- |
| `SEY-CTR-C01` | `SEY-CTR-V01` |
| `SEY-DNE-C01` | `SEY-DNE-V01` |
| `contrast inside I-AA` | `I-AA` |
| `contrast inside I-AL` | `I-AL` |
| `contrast inside I-AO` | `I-AO` |
| `contrast inside I-C3` | `I-C3` |
| `contrast inside I-C4` | `I-C4` |
| `contrast inside I-CASE2` | `I-CASE2` |
| `contrast inside I-CASE3` | `I-CASE3` |
| `contrast inside I-CS` | `I-CS` |
| `contrast inside I-DAO` | `I-DAO` |
| `contrast inside I-DOA` | `I-DOA` |
| `contrast inside I-FA` | `I-FA` |
| `contrast inside I-FO` | `I-FO` |
| `contrast inside I-OM` | `I-OM` |

The connective labels are nearest-error decisions inside their introduction
puzzles. The two classical labels are already-taught polarity decisions retained
inside the named later application puzzles. None of these 15 labels is emitted as
a puzzle ID, and every source label remains traceable through its owner.

## Shared puzzle relationships

“Shared” here means one emitted puzzle record supports two or more distinct skill
IDs. There are 63 such records. Every supported skill and evidence role follows.

### Structural

| Puzzle | Supported skill/role relationships |
| --- | --- |
| `paired-veil-eligibility-contrast` | `release-paired-veils` (contrast); `resolve-repeated-veils` (contrast); `release-content-bearing-veils` (contrast); `wrap-content-in-paired-veils` (contrast) |
| `erase-insert-polarity-contrast` | `clear-dark-field` (contrast); `insert-complete-fragment` (contrast) |
| `echo-copy-contrast` | `lift-supported-echo` (contrast); `copy-supported-fragment` (contrast) |
| `owner-scope-contrast` | `trace-single-mark-ownership` (contrast); `distinguish-nested-owners` (contrast) |
| `timeline-scrub-branch-contrast` | `rewind-and-compare` (contrast); `replace-retained-future` (contrast) |
| `weakening-projection-contrast` | `prove-weakening` (contrast); `select-needed-conjunct` (contrast) |
| `injection-branch-contrast` | `choose-left-injection` (contrast); `choose-right-injection` (contrast) |
| `contraction-idempotence-contrast` | `copy-supported-fragment` (contrast); `prove-conjunction-idempotence` (contrast); `prove-disjunction-idempotence` (contrast) |
| `exchange-scope-contrast` | `recognize-conjunction-exchange` (contrast); `recognize-disjunction-exchange` (contrast) |
| `reassociation-scope-contrast` | `recognize-conjunction-reassociation` (contrast); `recognize-disjunction-reassociation` (contrast) |
| `mixed-content-double-cuts` | `release-paired-veils` (application, mixed); `release-content-bearing-veils` (application, mixed); `wrap-content-in-paired-veils` (application, mixed) |
| `delayed-veils-fields` | `release-paired-veils` (application, retrieval, mixed); `resolve-repeated-veils` (application, retrieval, mixed); `clear-dark-field` (application, retrieval, mixed); `lift-supported-echo` (application, mixed); `rewind-and-compare` (application, retrieval, mixed); `replace-retained-future` (application, retrieval, mixed) |
| `timeline-route-weave` | `resolve-repeated-veils` (application, mixed); `rewind-and-compare` (application, mixed); `replace-retained-future` (application, mixed); `release-content-bearing-veils` (application, retrieval, mixed) |
| `polarity-edit-weave` | `clear-dark-field` (application, mixed); `trace-single-mark-ownership` (application, mixed); `read-region-polarity` (application, mixed); `insert-complete-fragment` (application, mixed) |
| `delayed-rings-echoes` | `lift-supported-echo` (application, retrieval, mixed); `trace-single-mark-ownership` (application, retrieval, mixed); `distinguish-nested-owners` (application, retrieval, mixed) |
| `projection-reassociation-weave` | `distinguish-nested-owners` (application, mixed); `select-needed-conjunct` (application, mixed); `choose-right-injection` (application, mixed); `recognize-conjunction-reassociation` (application, mixed) |
| `contraction-idempotence-weave` | `read-region-polarity` (application, retrieval, mixed); `wrap-content-in-paired-veils` (application, retrieval, mixed); `copy-supported-fragment` (application, mixed); `prove-conjunction-idempotence` (application, mixed) |
| `disjunction-idempotence-weave` | `insert-complete-fragment` (application, retrieval, mixed); `prove-disjunction-idempotence` (application, mixed); `recognize-disjunction-exchange` (application, mixed); `recognize-disjunction-reassociation` (application, mixed) |
| `weakening-injection-weave` | `prove-weakening` (application, mixed); `choose-left-injection` (application, mixed); `recognize-conjunction-exchange` (application, mixed) |
| `conjunction-structural-capstone` | `prove-weakening` (application, retrieval, mixed); `select-needed-conjunct` (application, retrieval, mixed); `copy-supported-fragment` (application, retrieval, mixed); `prove-conjunction-idempotence` (application, retrieval, mixed); `recognize-conjunction-exchange` (application, retrieval, mixed); `recognize-conjunction-reassociation` (application, retrieval, mixed) |
| `disjunction-structural-capstone` | `choose-left-injection` (application, retrieval, mixed); `choose-right-injection` (application, retrieval, mixed); `prove-disjunction-idempotence` (application, retrieval, mixed); `recognize-disjunction-exchange` (application, retrieval, mixed); `recognize-disjunction-reassociation` (application, retrieval, mixed) |
| `mixed-structural-synthesis` | `prove-weakening` (challenge); `select-needed-conjunct` (challenge); `choose-left-injection` (challenge); `choose-right-injection` (challenge) |
| `transfer-seyric-mechanics` | `release-paired-veils` (transfer); `resolve-repeated-veils` (transfer); `clear-dark-field` (transfer); `lift-supported-echo` (transfer); `read-region-polarity` (transfer); `insert-complete-fragment` (transfer); `release-content-bearing-veils` (transfer); `wrap-content-in-paired-veils` (transfer) |
| `transfer-timeline-branch` | `rewind-and-compare` (transfer); `replace-retained-future` (transfer) |
| `transfer-duplication-recognition` | `copy-supported-fragment` (transfer); `prove-conjunction-idempotence` (transfer); `prove-disjunction-idempotence` (transfer); `recognize-conjunction-reassociation` (transfer); `recognize-disjunction-reassociation` (transfer) |
| `transfer-structural-choice` | `trace-single-mark-ownership` (transfer); `distinguish-nested-owners` (transfer); `prove-weakening` (transfer); `select-needed-conjunct` (transfer); `choose-left-injection` (transfer); `choose-right-injection` (transfer); `recognize-conjunction-exchange` (transfer); `recognize-disjunction-exchange` (transfer) |
| `remediate-polarity-gates` | `clear-dark-field` (remediation); `read-region-polarity` (remediation); `insert-complete-fragment` (remediation) |
| `remediate-timeline-branching` | `rewind-and-compare` (remediation); `replace-retained-future` (remediation) |
| `remediate-double-cut-annulus` | `release-content-bearing-veils` (remediation); `wrap-content-in-paired-veils` (remediation) |
| `remediate-weakening-projection` | `prove-weakening` (remediation); `select-needed-conjunct` (remediation) |
| `remediate-injection-choice` | `choose-left-injection` (remediation); `choose-right-injection` (remediation) |
| `challenge-exchange-near-match` | `distinguish-nested-owners` (challenge); `recognize-conjunction-exchange` (challenge); `recognize-disjunction-exchange` (challenge) |
| `challenge-reassociation-near-match` | `recognize-conjunction-reassociation` (challenge); `recognize-disjunction-reassociation` (challenge) |

### Connective

| Puzzle | Supported skill/role relationships |
| --- | --- |
| `B1` | `compose-3` (application); `and-lift` (application) |
| `B2` | `compose-4` (application); `case-2` (application) |
| `B3` | `compose-side` (application); `or-map` (application); `case-2` (application) |
| `B4` | `compose-3` (application); `distribute-and-over-or` (application); `factor-common-and` (application) |
| `B5` | `compose-4` (application); `distribute-or-over-and` (application); `factor-common-or` (application) |
| `B8` | `distribute-and-over-or` (application); `factor-common-or` (application) |
| `B9` | `case-3` (application); `factor-common-and` (application); `distribute-or-over-and` (application) |
| `B7` | `and-lift` (application); `or-map` (application); `absorb-or` (application) |
| `B10` | `compose-side` (application); `case-3` (application); `absorb-and` (application); `absorb-or` (application) |
| `R2` | `compose-4` (retrieval); `and-lift` (retrieval); `or-map` (retrieval); `case-2` (retrieval) |
| `R3` | `compose-side` (retrieval); `distribute-and-over-or` (retrieval); `distribute-or-over-and` (retrieval) |
| `R4` | `factor-common-and` (retrieval); `absorb-and` (retrieval) |
| `R5` | `case-3` (retrieval); `factor-common-or` (retrieval); `absorb-or` (retrieval) |
| `T1` | `compose-3` (transfer, mixed); `compose-4` (transfer, mixed); `compose-side` (transfer, mixed); `and-lift` (transfer, mixed); `or-map` (transfer, mixed) |
| `T2` | `case-2` (transfer, mixed); `case-3` (transfer, mixed); `distribute-and-over-or` (transfer, mixed); `factor-common-and` (transfer, mixed); `distribute-or-over-and` (transfer, mixed); `factor-common-or` (transfer, mixed) |
| `T3` | `absorb-and` (transfer, mixed); `absorb-or` (transfer, mixed) |
| `CH-COMP` | `compose-3` (challenge); `compose-4` (challenge); `compose-side` (challenge) |
| `CH-CASE` | `case-2` (challenge); `case-3` (challenge) |
| `CH-DIST-AND` | `distribute-and-over-or` (challenge); `factor-common-and` (challenge) |
| `CH-DIST-OR` | `distribute-or-over-and` (challenge); `factor-common-or` (challenge) |
| `CH-ABS` | `absorb-and` (challenge); `absorb-or` (challenge) |

`B6`, `R1`, `CH-AND`, and `CH-OR` are emitted once but are not in this table
because each supports only one skill ID in the normalized roadmap.

### Classical/reference

| Puzzle | Supported skill/role relationships |
| --- | --- |
| `SEY-DM-R01` | `expand-negated-conjunction` (retrieval); `factor-negated-conjunction` (retrieval); `expand-negated-disjunction` (retrieval); `factor-negated-disjunction` (retrieval) |
| `SEY-DM-R02` | `factor-negated-conjunction` (retrieval); `expand-negated-conjunction` (retrieval); `expand-negated-disjunction` (retrieval); `factor-negated-disjunction` (retrieval) |
| `SEY-CL-R01` | `content-double-negation` (retrieval); `excluded-middle` (retrieval); `reductio` (retrieval); `peirce-feedback` (retrieval) |
| `SEY-XFER-V01` | `direct-contraposition` (transfer, mixed); `structural-variant-transfer` (application) |
| `SEY-XFER-V02` | `expand-negated-conjunction` (transfer, mixed); `factor-negated-conjunction` (transfer, mixed); `expand-negated-disjunction` (transfer, mixed); `factor-negated-disjunction` (transfer, mixed); `structural-variant-transfer` (application) |
| `SEY-XFER-V03` | `content-double-negation` (transfer, mixed); `excluded-middle` (transfer, mixed); `reductio` (transfer, mixed); `peirce-feedback` (transfer, mixed) |
| `SEY-XFER-R01` | `exact-reference-selection` (retrieval); `manifest-reference` (retrieval); `dissolve-reference` (retrieval); `structural-variant-transfer` (retrieval) |
| `SEY-XFER-V04` | `exact-reference-selection` (transfer, mixed); `manifest-reference` (transfer, mixed); `dissolve-reference` (transfer, mixed); `structural-variant-transfer` (mixed) |
| `SEY-XFER-T01` | `structural-variant-transfer` (transfer); `exact-reference-selection` (transfer) |

## Self-audit against the approved design

- No family heading became either a skill or a puzzle.
- The six existing Seyric puzzle IDs remain exact: `two-veils`, `four-veils`,
  `forked-veil`, `echoed-veil`, `single-mark-return`, and
  `two-mark-projection`.
- Required nested-owner evidence begins at `nested-owner-introduction` and continues
  through required contrast, application/retrieval/mixed, and transfer records.
  Optional `two-mark-projection` contributes challenge evidence only and is not in
  the final-transfer closure.
- Every one of the 49 skills has at least one introduction, one contrast, two
  distinct applications, one retrieval, one mixed record, and one transfer record.
- The complete optional complement lies outside the final-transfer closure and
  consists only of remediation/challenge records. In particular,
  `mixed-structural-synthesis` is a bounded optional challenge, while `T3` remains
  required.
- Every puzzle has exactly one primary evidence relationship, stored first; shared
  relationships do not create duplicate puzzle identities.
- No production puzzle content was authored during inventory normalization.

## Direct verification evidence

The factual roadmap audit command was:

```text
node /tmp/cursebreaker-normalization-receipt.7lrx2x/audit.mjs
```

It reported 49 skills, 186 puzzles, stage partitions 23/64, 13/51, and
13/71; 186 unique folio positions from 0 through 185; zero duplicate IDs,
unresolved references, cycles, or missing evidence categories; final transfer
`SEY-XFER-T01`; closure 140/46 with stage partitions 51/13, 31/20, and
58/13; `T3` present in closure; and `mixed-structural-synthesis` absent from
closure. Its derived shared-record set contains the 63 records tabulated above.

The direct contract test command was:

```text
npx vitest run tests/game/seyric-roadmap.test.ts
```

It passed all 6 tests. The closure test directly asserts 140 required, 46 optional,
and that every optional record contains only remediation or challenge evidence.

The final focused commands were:

```text
npx vitest run tests/game/seyric-roadmap.test.ts tests/game/content-validation.test.ts tests/game/layered-content.test.ts
npm run content:validate
git diff --check
```

The focused run passed 15 tests in 3 files. Content validation reported 7 puzzles,
7 solutions, and 1 recognized state. `git diff --check` produced no diagnostics.
