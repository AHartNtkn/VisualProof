# Atomic proof spawning and graphical-insertion removal

## Outcome

General graphical insertion no longer exists in the kernel, proof model, serialization, application, bundled derivations, tests, or examples. Players construct proof diagrams through the same contextual spawn cascade used in Edit: closed terms, loaded named relations, and enclosing bound relations appear through their existing or atomic operations wherever each operation is valid.

Named relation spawning and bound-relation spawning are available in the same Proof contexts. A bound relation additionally requires a compatible enclosing bubble and retains the previously approved colored-circle and complete binder-subtree hover treatment.

## Proof construction vocabulary

Two atomic spawning operations replace arbitrary insertion:

1. **Named relation spawn** creates one reference node for a currently loaded relation, with one fresh singleton argument wire per boundary position. It is valid only in an insertion-polarity region: negative while proving forward and positive while proving backward, and revalidates the relation id and arity at commit time.
2. **Bound relation spawn** creates one atom node bound to a chosen enclosing bubble, with one fresh singleton argument wire per binder argument. It has the same polarity gate and additionally requires the chosen bubble to enclose the invocation region with matching live arity.

The existing `closedTermIntro` rule remains the sole Proof spawning route for a λ-term. The spawn cascade continues to route closed term input through `closedTermIntro` and refuses open terms. Open term nodes are derived through the existing conversion/fission, iteration, relation, and wiring operations rather than a duplicate term-spawn rule.

Each new atomic step stores only its semantic input—region and relation id/arity, or region and binder—not an embedded `DiagramWithBoundary`. Appliers construct exactly one node plus required singleton wires and revalidate through `mkDiagram`. They do not accept preassembled subgraphs, attachments, binder maps, or arbitrary patterns.

## Shared contextual interaction

`SpawnCascade` remains the single presentation and interaction owner in Edit, comprehension editing, ordinary Proof, and both fixed proof fronts. Proof hosts provide the live relation context and `boundPredicateOptions(currentDiagram, invocationRegion)` instead of empty catalogs.

The cascade presents:

- `λ term…` for the existing closed-term introduction;
- loaded named relations, grouped and searchable by namespace; and
- every enclosing bound relation, ordered innermost to outermost.

The same contextual right-click gesture opens the cascade in every host. Host differences are limited to commit policy:

- Edit uses `addTermNode`, `addRefNode`, and `addAtomNode` and pushes Edit history.
- Proof records the matching atomic proof step through the active forward/backward timeline and seeds the introduced node at the invocation point.
- Comprehension editing retains its current draft/host transaction policy.

No Proof-only catalog, duplicate menu, or separate bound-relation chooser exists.

## Bound-relation identity and highlighting

The design introduced in commit `75926f6` is authoritative and must operate unchanged in Proof:

- Each bound-relation row has a circular swatch colored from the renderer’s authoritative bubble hue.
- Nested choices are labelled by binder order and arity, distinguishing innermost and outermost binders.
- Hovering a row highlights the complete group owned by that binder, not merely the bubble circumference or prospective atom.
- Moving away, closing the cascade, switching focus/front/mode, committing, refusing, or disposing clears the cascade-owned binder highlight.

Main Proof can reuse the shell’s existing `spawnHoverBinder` paint path. Each fixed proof front owns an equivalent transient hovered-binder id and adds `highlightGroup` output to that front’s rendered overlay. The highlight is view-only and never mutates proof state.

## Legality and refusal

Forward atomic spawning requires a negative invocation region. Backward atomic spawning requires a positive invocation region. The same applier implements both orientations by flipping only that gate.

At commit time:

- closed-term parsing and structural validity are rechecked by `closedTermIntro`;
- named relations must still exist and retain the displayed arity;
- bound relation binders must still exist, be bubbles, retain their displayed arity, and enclose the invocation region; and
- every new wire is scoped at the invocation region.

A refusal leaves the cascade open when correction remains possible, records no proof step, preserves diagram identity and timeline cursor, and displays the kernel-compatible reason at the invocation point.

## Graphical-insertion deletion

The following model is removed rather than deprecated:

- `applyInsertion` and its kernel export;
- the `ProofStep` insertion variant;
- application, orientation, ID-composition, JSON read/write, and action-discovery cases;
- the Proof `Insert…` action and typed insertion prompt;
- extraction/insertion theory macros;
- direct insertion tests and polarity-matrix expectations;
- every bundled derivation step and generated JSON occurrence carrying `rule: "insertion"`.

There is no alias, compatibility decoder, legacy step, private arbitrary-pattern wrapper, or fallback splice route. Loading a file containing an insertion step fails as an unknown proof rule.

`spliceSubgraph` and `DiagramWithBoundary` remain for concepts that genuinely consume diagrams with boundaries—iteration, theorem application, relation definitions, and comprehension—not as a proof-construction escape hatch.

## Derivation migration

Each existing bundled insertion is reconstructed with ordinary steps. Flat term patterns use the existing closed-term-introduction plus conversion/fission construction path already embodied by the theory’s `kOpen` helper; references and bound relations use their atomic spawns, followed by wire joins. Open attachment positions are realized by joining the spawned singleton wire to the existing host wire under the same polarity gate.

Nested guard and closure patterns are redesigned as actual derivations using the existing structural vocabulary: double-cut introduction/elimination, vacuous bubbles, atomic spawns, iteration/deiteration, comprehension abstraction/instantiation, relation fold/unfold, and wire operations. The migration must preserve each theorem’s declared boundary and final boundary-pinned canonical form; reproducing old intermediate ids or shapes is not required.

If a migration appears to require arbitrary pattern splicing, that is treated as evidence of a missing atomic interaction or an unnecessarily indirect proof, not justification for retaining graphical insertion.

Generated `examples/frege.json` is regenerated from the migrated authoritative TypeScript theory builder.

## Validation

Kernel and proof tests establish:

- forward/backward polarity gates for both new atomic spawns and unchanged polarity-blind closed-term introduction;
- exact singleton-wire construction and binder-scope validation;
- replay, composition-id mapping, undo/redo, and JSON round trips for atomic steps;
- rejection of the removed insertion rule in JSON;
- no arbitrary embedded pattern in any spawn step; and
- every migrated theorem verifies with its intended boundary-pinned result.

Interaction and browser tests establish:

- main forward/backward Proof and both fixed fronts expose loaded named relations and valid bound relations;
- nested binders retain deterministic ordering, colored circular swatches, arity labels, and complete subtree hover highlighting;
- committing each option places exactly one node and advances only the owning timeline;
- invalid polarity, stale relation arity, missing relation, and invalid binder scope refuse without mutation;
- menu, hover, focus, mode, front, and disposal cleanup; and
- Edit and comprehension behavior remain unchanged.

Architecture audits search source, tests, generated examples, and serialized fixtures for the displaced insertion model. Typecheck and every ordinary test must pass. Physics code is unaffected, so the opt-in physics suite is not run.
