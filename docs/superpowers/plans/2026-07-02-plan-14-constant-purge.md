# Plan 14: The Constant Purge — named definitions are nodes, never term syntax

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Enforce the USER LAW (memory: `named-defs-never-inside-terms`, 2026-07-02): *"Relations are ALWAYS AND ONLY EVER THEIR OWN NODES … THERE ARE NO NODES ASSOCIATED WITH LAMBDA EXPRESSIONS … The definition of named relations can expand to diagrams that include lambda expressions, but THAT'S IT."* The violation that exposed the wrong model: dragging a λ-term body dragged its satellite constant discs with it — because the KERNEL term language contains constants inside terms.

**The target model:**
- λ-term nodes carry PURE λ-terms: `bvar | port | lam | app`. The `const` constructor is deleted from the term language.
- Every named definition is a RELATION: a ref node `{kind:'ref', defId, arity}` whose definition is a `DiagramWithBoundary`. Function constants become relations with an output place: `Zero/1`, `Succ/2`, `Plus/3`. The defining diagram wires a closed pure-λ program node to a use-site term node by a line of identity (e.g. Plus(a,b,c) := ∃p. p = ⟦λm n f x. m f (n f x)⟧ ∧ c = p a b).
- Connections between named nodes and λ-term nodes happen ONLY by shared wires (lines of identity). Definitional computation happens by `fusion` (the one-point rule, inlines a producer along its wire) + `conversion` (βη) + `fission` (extract), replacing the deleted term-level `unfold`/`fold`.
- The renderer's satellite mechanism (constant discs attached to term bodies) is deleted with the glyphs that fed it. Nothing is ever visually attached to a λ-term's anatomy.

**Ordering constraint:** the restated theories only use machinery that already exists (relUnfold/relFold, fusion/fission, conversion, closedTermIntro, comprehension, congruenceJoin, headStrip). So the theories are restated FIRST on the current kernel — the suite stays green at every commit — and the purge lands second, compiler-driven, once nothing references constants.

### Task 0: Spike — one relational derivation end to end

De-risk the machinery before committing to the restatement: in a scratch vitest, define `Zero/1` and `Plus/3` as relations (defining diagrams with internal program wires), state relational `plusLeftUnit` (lhs: Zero(z) ∧ Plus(z,a,o); rhs: the o and a boundary ports riding one wire), and derive it via relUnfold → fusion → conversion → wire joins. Record the exact step sequence and every gate hit (fusion's single-consumer requirement, scope gates, boundary handling).

- [x] Spike green in a scratch test; findings recorded in this doc (§ Spike findings). Scratch deleted.

### Task 1: Relational restatement of the theories (current kernel, no purge yet)

**Files:** `src/theories/frege.ts` (relations `zero/1`, `succ/2`, `plus/3`, `nat/1` restated pure — the nat body uses Zero/Succ REF nodes per the user's round-3 directive, no bare λ in the definition; theorems `plusAssoc`, `plusLeftUnit`, `plusRightUnit`, `succShiftS`, `plusComm` restated relationally with the same names and re-derived), `src/theories/lambda.ts` (same treatment for whatever it defines), `src/theories/macros.ts` as needed.
**Test:** `tests/theories/*` batteries updated to the relational statements; `checkTheorem` green for every theorem; the battery asserts the statements contain NO `const` term anywhere (guards the coming purge).

- [ ] All five arithmetic theorems re-derived relationally, batteries green, suite + tsc green. Commit.

### Task 2: The purge (kernel + view + app)

**Files:** `src/kernel/term/term.ts` (`const` constructor deleted; `cnst` deleted), knock-ons compiler-surfaced in `parse.ts` (constNames parameter deleted — `parseTerm(s)`), `print.ts`, `serialize.ts`, `reduce.ts`, `hnf.ts`, `path.ts`, `matchkey.ts`, `shape.ts`; `src/kernel/rules/definitions.ts` DELETED (applyUnfold/applyFold, Definitions type); proof steps `unfold`/`fold` deleted from `step.ts` + `json.ts`; `ProofContext.definitions` deleted; `headstrip.ts` const-head refusal branch deleted (unreachable); `src/view/tromp.ts`/`bend.ts` glyph geometry deleted; `src/view/engine.ts` Satellite type + satellites deleted; `paint.ts`/`hittest.ts` satellite painting/hit targets deleted; `src/app/boot.ts`/`shell.ts`/`tactics.ts` constNames plumbing deleted; `store.ts`/`persist.ts` theory JSON format drops definitions (no legacy readers — the format changes, the emitters regenerate).
**Test:** law battery gains: mkEngine produces zero satellites for every bundled diagram (the concept is gone — the test asserts the display list contains labels ONLY at ref-node discs); serialization round-trips have no const case; full suite + tsc green with the deletions (no wrappers, no re-exports).

- [ ] Purge complete, `grep -rn "cnst\|'const'\|constNames\|constId" src/` returns nothing, suite + tsc + e2e green. Commit.

### Task 3: Examples, e2e, review, sync

- [ ] `scripts/emit-theories.ts` regenerates `examples/*.json` in the new format; e2e green (replay of relational plusComm through the live shell).
- [ ] Independent adversarial review (reviewer wrote none of the code): mutation probes — reintroduce a satellite → law test fails; smuggle a const-like label onto term anatomy → law-2 fails; check every derivation replays from JSON through `loadTheory` (not just from builders); hunt for leftover definitions plumbing.
- [ ] Plan-doc sync; memory update (`named-defs-never-inside-terms` gains the integration state); merge.

---

### Spike findings (Task 0)

Green first run (relational plusLeftUnit, 5 steps: relUnfold ×2, fusion ×2, conversion):
- A relation definition whose body wires a closed pure-λ program node to a use-site term node splices cleanly: `applyRelUnfold` merges the body's boundary stubs into the reference's arg wires, and the OUTER wire ids (the theorem's boundary) survive unfolding and fusion — `mkDiagramWithBoundary(cur, [wa, wo])` works on the final diagram with the original ids.
- `fusion`'s gates (exactly producer-output + one consumer-freeVar endpoint on the wire; producer at the wire's scope) are satisfied naturally by definition wires as built. After fusing the program wire, the zero wire becomes the next producer/consumer pair — fusions chain without preparation.
- `conversion` with a recorded certificate replays fuel-free on the fused pure term; the target `port(a)` (o = a) is the relational form of the old `target: port('s0')` recipes.
- `ProofContext.definitions` is still a required field (`{}` works) — it dies in Task 2.
- Port names inside relation bodies are freshened by the splice; derivation code must locate spliced nodes/wires STRUCTURALLY (by term shape / endpoint pattern), never by name — consistent with the port-name law.
