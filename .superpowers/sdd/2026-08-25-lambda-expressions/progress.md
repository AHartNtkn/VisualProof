# SDD ledger — plan: docs/superpowers/plans/2026-08-25-lambda-expressions.md

Branch: `feature/lambda-expressions`
Plan start: `1280a15a29720f97bd1fe36891b658b07aba9f1e`
Spec: `docs/superpowers/specs/2026-08-25-lambda-expressions-design.md`

## Preflight task consistency

| Task | Internal agreement check | Result |
|---|---|---|
| 1 | Tests cover nameless structure, parsing, reduction, normalization, paths, serialization, and certificates; listed modules implement those surfaces. | Clean |
| 2 | Term-node invariant, canonical participation, JSON, and subgraph tests exercise every listed diagram integration point. | Clean |
| 3 | Parser, translator, palette, and application-entry edits jointly cover whole-term formula operands. | Clean |
| 4 | Focused rule tests and proof replay tests cover the two dedicated rules and all listed proof registries. | Clean |
| 5 | Tromp, bend, engine, paint, and hit tests cover the listed 2D geometry and ownership integration. | Clean |
| 6 | Spawn/menu/cap, conversion, undo, replay, and persistence tests cover all listed application and proof files. | Clean |
| 7 | Rule-level and interaction-level tests cover fission/fusion, congruence, head strip, anchored wire, copying, connection, and proof-front behavior. | Clean |
| 8 | Phase, correspondence, color-lineage, and application-motion tests cover the shared motion planner and both consumers. | Clean |
| 9 | Planarity, branch-normal orientation, no-fill, color, picking, layout, and transition tests cover all listed 3D integrations. | Clean |
| 10 | Complete Lambda definitions precede model integration; compilation and no-admission checks validate the stated foundation. | Clean |
| 11 | The new Lean item is propagated through its full recursor/semantics dependency closure before semantic GREEN. | Clean |
| 12 | Rule witnesses precede soundness, evidence registration, and exact runners; every production theorem follows RED/GREEN. | Clean |
| 13 | Each remaining formal relation is defined, proved, registered, and made exactly executable before validation. | Clean |
| 14 | Browser scenarios and persistence/pipeline fixtures cover the completed TypeScript and Lean-facing step surface. | Clean |
| 15 | Deterministic reference/app captures, measurements, direct inspection, and repair/rerun steps cover all required examples and modes. | Clean |
| 16 | Full TypeScript, browser, Lean, repository, ownership, and specification checks directly validate the requested outcome. | Clean |

## Preflight shared files and interfaces

| Tasks | Producer / consumer or shared owner | Result |
|---|---|---|
| 1 → 2 | Nameless `Term`, `freeArity`, and well-formedness feed term diagram nodes. | Compatible |
| 1 → 3 | `ParsedTerm` and canonical slots feed formula operands. | Compatible |
| 1 → 4 | Terms, normalization, paths, and certificates feed conversion rewrites. | Compatible |
| 1 → 5 | Terms and occurrence paths feed Tromp geometry. | Compatible |
| 1 → 7 | Occurrence paths feed subterm interactions. | Compatible |
| 1 → 8 | Terms and reduction steps feed structural motion. | Compatible |
| 2 → 3 | Formula translation consumes signature-indexed term-node construction. | Compatible |
| 2 → 4 | Dedicated rules rewrite the term and identity nodes introduced by Task 2. | Compatible |
| 2 → 5 | 2D rendering consumes term node ports and structure. | Compatible |
| 2 → 6 | Spawn rules consume `spawnTermNode` and cap its incidences. | Compatible |
| 2 → 7 | Interaction rewrites preserve Task 2 diagram invariants. | Compatible |
| 2 ↔ 11 | TypeScript and Lean term nodes share the approved whole-term/signature-indexed representation. | Compatible |
| 3 ↔ 6 | `src/app/shell.ts` combines formula entry with the restored Lambda interaction menu. | Compatible; later task extends the same owner |
| 4 ↔ 6 | Lambda exports plus proof step/JSON/compose registries gain spawn after conversion and identity. | Compatible; exhaustive switches extended incrementally |
| 4 ↔ 7 | The same rule and proof registries gain the remaining Lambda operations. | Compatible; later task extends the same owner |
| 4 ↔ 12 | Lean conversion and free-variable identity formalize the TypeScript operations. | Compatible |
| 5 → 7 | Occurrence geometry feeds selection and fission interaction. | Compatible |
| 5 ↔ 8 | `src/view/paint.ts` gains motion sampling after static term paint. | Compatible; Task 8 extends Task 5 |
| 5 → 9 | 3D embedding consumes the 2D term geometry as its planar source. | Compatible |
| 6 ↔ 7 | Lambda exports, proof registries, moves, and shell gain additional interactions. | Compatible; later task extends the same switches |
| 6 → 13 | Lean spawn relation formalizes the replayable TypeScript spawn operation. | Compatible |
| 6 → 14 | Browser, replay, and persistence coverage exercise the spawn and conversion surface. | Compatible |
| 7 → 13 | Lean relations formalize fission/fusion, congruence, head strip, and anchored-wire operations. | Compatible |
| 7 → 14 | End-to-end scenarios consume the completed interaction surface. | Compatible |
| 8 → 9 | 3D transitions sample the shared Lambda motion and color frames. | Compatible |
| 8 → 15 | Reference capture measures the corrected phase geometry and color lineage. | Compatible |
| 9 → 14 | Browser coverage exercises 3D scene creation and picking. | Compatible |
| 9 → 15 | Reference capture measures 3D planarity, orientation, geometry, and color. | Compatible |
| 10 → 11 | Intrinsically scoped terms and `Model.toLambdaModel` feed diagram items and denotation. | Compatible |
| 10 → 12 | Beta-eta semantics and the lawful model feed conversion soundness. | Compatible |
| 10 → 13 | Lambda calculus and model laws feed the remaining rule proofs. | Compatible |
| 11 → 12 | Lean term items and denotation feed the two core Lambda relations. | Compatible |
| 11 → 13 | Lean term items and diagram algebra feed the remaining relations. | Compatible |
| 12 ↔ 13 | Lambda rule, soundness, executable, and Step aggregators are extended in sequence. | Compatible; Task 13 builds on Task 12 |
| 12–13 → 14 | Complete registered step evidence feeds pipeline, snapshot, session, and theory-emission coverage. | Compatible |
| 14 → 15 | The loadable application workflows provide the runtime under deterministic capture. | Compatible |
| 1–15 → 16 | Final validation consumes every implemented and tested surface without changing ownership. | Compatible |

Preflight result: no contradictions with the specification or Global Constraints; no plan-mandated defective tests or duplicated logic blocks found.

Task 1: review ⚠ resolved — the implementer report records the focused Vitest command and 55/55 passing output, plus `npm run typecheck` exiting 0 with no diagnostics.
Task 1: complete (commits 1280a15a..45144030, review clean)
Task 2: complete (commits 45144030..57f63472, review clean)
Task 3: fix round 1/5 (1 addressed, 0 open — primed Lambda identifiers accepted by formula tokenization; commits 791ba259..bb8bd927)
Task 3: complete (commits 57f63472..bb8bd927, review clean)
Task 4: review ⚠ resolved — the implementer report records 14 focused files and 119 tests passing, plus `npm run typecheck` exiting successfully.
Task 4: complete (commits bb8bd927..e9f576ac, review clean)
Task 5: fix round 1/5 (2 addressed, 0 open — explicit unused interface rails/anchors and cross-body hit precedence; commits cbecd4c3..fc80f959)
Task 5: complete (commits e9f576ac..fc80f959, review clean)
Task 6: review ⚠ resolved — the implementer report records 42 required tests and 325 broad regression tests passing, plus successful typechecking.
Task 6: complete (commits fc80f959..901bb9db, review clean)
Task 7: minor (deferred): connection candidate probing catches every thrown value, so unexpected implementation failures could be treated as rule inapplicability; final review must triage typed expected-error handling.
Task 7: fix round 1/5 (2 addressed, 0 open — aliased native-slot fission/fusion and physical-carrier correspondence; commits 45d7b98c..2dd402ad)
Task 7: complete (commits 901bb9db..2dd402ad, review clean; 1 deferred minor)
Task 8: fix round 1/5 (3 addressed, 1 open — live 2D lifecycle, identify binder color, strict consumed-stroke classification addressed; reverse manual lifecycle mapping newly open; commits 58a4faa8..5eafe5fa)
Task 8: fix round 2/5 (1 addressed, 0 open — reverse scrub/play/step/history presentation mapping; commits 5eafe5fa..a61a792c)
Task 8: complete (commits 2dd402ad..a61a792c, review clean)
Task 9: minor (deferred): static Lambda radial role metadata collapses structural output/argument connector distinctions into `fn-connector`; final review must triage metadata consistency.
Task 9: review ⚠ resolved — source-level theme colors are exact; Task 15 will provide the requested rendered light/dark evidence under the real renderer.
Task 9: fix round 1/5 (4 addressed, 0 open — animated branch-derived pose, exact strand anchors, transient picking/focus, and missing transition coverage; commits a2e7e8c0..11467521)
Task 9: complete (commits a61a792c..11467521, review clean; 1 deferred minor)
Task 10: review ⚠ resolved — the report records direct module elaboration, the full 118-job build passing, and an empty repository-wide `sorry` scan.
Task 10: complete (commits 11467521..0438cfb1, review clean)
Task 11: Ruling: pull the complete formal Lambda Spawn slice and its structural support-leaf derivation forward from Task 13 after the term item/semantics are GREEN — the enlarged comprehension completeness theorem is otherwise false because arbitrary singleton terms have no derivation; weakening that theorem or inventing a structural term primitive would misstate the proof system — cost if wrong: Task 11's diff and review surface become larger, and Task 13 must treat Spawn as an already-completed dependency rather than implementing it again.
Task 11: Ruling: retain fresh/capped Lambda Spawn and add a distinct Lambda-owned comprehension term-leaf abstraction relation with its soundness/Step integration and support compiler, parallel in responsibility to the existing atom/identity leaf transforms — fresh spawn is semantically blank only on fresh local wires and cannot preserve the inherited-wire term predicate required by `SupportDerives`; conflating the operations or weakening completeness would be unsound — cost if wrong: a new formal Lambda rule family and substantial completeness proof surface are added beyond the original plan, and later aggregate-rule tasks must treat that family as established.
Task 11: review ⚠ resolved — the implementer report records the 133-job full build passing and an empty repository-wide `sorry` scan.
Task 11: complete (commits 0438cfb1..107f31ef, review clean)
Task 12: review ⚠ resolved — the implementer report records the 135-job full build passing and an empty repository-wide `sorry` scan.
Task 12: complete (commits 107f31ef..f36bce00, review clean)
Task 13: Ruling: preserve universal `Step.Evidence.sound` over `Model` and extend `Model` with the exact rigid-head argument-reflection law needed by HeadStrip, proving the canonical quotient model satisfies it — HeadStrip cannot recover argument equality in an arbitrary beta-eta-sound non-reflecting model, while making the entire proof calculus canonical-model-specific would weaken the existing compositional model-parametric architecture — cost if wrong: admissible models must now provide rigid-head separation, excluding lawful beta-eta models that intentionally identify additional terms.
Task 13: Ruling: extend the existing formal occurrence surface with a proof-relevant multi-site scoped rewrite witness carrying exact region addresses, endpoint partitions, replacement data, non-overlap/order, derived-scope destinations, and equality to the rebuilt target; use it for AnchoredWire split/contract — the TypeScript operation changes independently located regions and a one-hole occurrence cannot state the selected semantics, while weakening it to local pins would omit required destinations — cost if wrong: the formal diagram API gains a new multi-site rewrite abstraction and its transport/semantic lemmas, increasing proof surface beyond the original file list.
Task 13: fix round 1/5 (2 open — Fusion omits descendant-region consumers; AnchoredWire descendant-root wire/item addresses omit the `anchorLocals.length + selected.locals.length` prefix and can target the wrong carrier; review commit d35578c8)
Task 13: fix round 1/5 (2 addressed, 0 open — Fusion supports ancestor bridge scope with same-region or descendant consumers; nested descendant-root addresses include both local prefixes while true cut locals remain unshifted; commits c52b7208..03a20e37)
Task 13: complete (commits f36bce00..03a20e37, review clean)
