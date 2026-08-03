# Formula-to-Diagram Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let a user submit a typed logical formula in Edit mode and atomically create its corresponding existential-graph diagram.

**Architecture:** A new pure `src/formula` boundary owns immutable source syntax, parsing, type-to-signature elaboration, lexical binding, and translation into the existing authoritative `Diagram` through `src/theories/graph.ts`. A focused browser component owns the formula form and calls the sole `formulaToDiagram(source)` entry point; the shell only installs the returned diagram through its existing undoable `pushEdit` owner.

**Tech Stack:** TypeScript 5.5, Vitest 2, Playwright 1.60, browser DOM, the existing typed existential-graph kernel and graph construction API.

## Global Constraints

- Accept the supplied Unicode formula verbatim, including `∀`, `∃`, `→`, `⇒`, `&`, applications, grouped binders, and default-individual untyped binders.
- Preserve and do not stage or modify `VisualProof/Diagram/Concrete/WirePrimitive/LeavesSemantics.lean`, `docs/goals/primitive-wire-quantifier-lean-completion/state.yaml`, or `tests/architecture/lean-semantics.test.ts`.
- There is exactly one production formula-to-diagram path: `formulaToDiagram(source: string): Diagram`.
- Formula submission is available only in Edit mode, replaces the displayed edit diagram atomically, and participates in existing Undo history.
- Parse/type failures are source-positioned, remain inline beside the formula field, and never partially mutate the diagram.
- Do not add parser dependencies, compatibility translators, direct-render paths, or formula-specific diagram representations.

---

### Task 1: Source-Located Formula Language

**Files:**
- Create: `src/formula/syntax.ts`
- Create: `src/formula/parse.ts`
- Create: `tests/formula/parse.test.ts`

**Interfaces:**
- Consumes: `Sig`, `IOTA`, and `relSig` from `src/kernel/diagram/sig.ts`.
- Produces: `SourceSpan`, `FormulaBinder`, `Formula`, `FormulaError`, and `parseFormula(source: string): Formula`.

- [ ] **Step 1: Write failing parser tests**

Add tests with the exact example source constant. Assert its outer AST is `forall Z`, then `forall S`, with signatures `relSig([IOTA])` and `relSig([IOTA, IOTA])`; assert `∀ n m.` creates two `IOTA` binders; assert implication is right-associative and conjunction binds more tightly. Add acceptance cases for `forall`/`exists`, `->`/`=>`, and `∧`. Add rejection cases for an unknown character, a missing body, duplicate binders in one quantifier, an unrepresentable `i → i` type, and an unbound application name, each matching `line 1, column N`.

- [ ] **Step 2: Run the parser tests and verify they fail**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts`

Expected: FAIL because `src/formula/parse.ts` does not exist.

- [ ] **Step 3: Define immutable syntax and source errors**

In `syntax.ts`, define:

```ts
export type SourceSpan = { readonly start: number; readonly end: number }

export type FormulaBinder = {
  readonly name: string
  readonly sig: Sig
  readonly span: SourceSpan
}

export type Formula =
  | { readonly kind: 'atom'; readonly name: string; readonly args: readonly string[]; readonly span: SourceSpan }
  | { readonly kind: 'and'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'implies'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'quantifier'; readonly quantifier: 'exists' | 'forall'; readonly binders: readonly FormulaBinder[]; readonly body: Formula; readonly span: SourceSpan }

export class FormulaError extends Error {
  readonly offset: number
  constructor(source: string, offset: number, message: string)
}
```

The error constructor computes one-based line and column and emits `${message} at line ${line}, column ${column}`. Freeze every AST node, binder array, and argument array returned by the parser.

- [ ] **Step 4: Implement tokenization, precedence, binders, types, and scope validation**

In `parse.ts`, tokenize identifiers, punctuation, `∀`/`forall`, `∃`/`exists`, `→`/`->`, `⇒`/`=>`, `&`/`∧`, and retain start/end offsets. Parse with these functions:

```ts
export function parseFormula(source: string): Formula
function parseImplication(): Formula
function parseConjunction(): Formula
function parsePrimary(): Formula
function parseQuantifier(): Formula
function parseType(): TypeExpression
function signatureOf(type: TypeExpression): Sig
```

Use right recursion for implication and a loop for conjunction. In a quantifier, apply one trailing annotation to every preceding name in that binder group (`∀ n m : i.`), default an unannotated group to `IOTA`, reject duplicate names inside that quantifier, and permit ordinary lexical shadowing in nested quantifiers. Translate `i` to `IOTA`, `o` to `relSig([])`, and a right-associated arrow chain ending in `o` to `relSig(domainSignatures)`; reject every arrow chain not ending in `o`. After parsing, walk the AST with a lexical environment and reject atom heads or arguments that are not bound, reject non-relation heads, and reject application arity/signature mismatches.

- [ ] **Step 5: Run parser tests and type checking**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts && npm run typecheck`

Expected: parser tests PASS and TypeScript reports no errors.

- [ ] **Step 6: Commit the parser authority**

Run:

```bash
git add src/formula/syntax.ts src/formula/parse.ts tests/formula/parse.test.ts
git commit -m "feat: parse typed logical formulas"
```

Before committing, verify `git diff --cached --name-only` contains exactly those three files.

---

### Task 2: Authoritative Formula-to-Diagram Translation

**Files:**
- Create: `src/formula/diagram.ts`
- Create: `src/formula/index.ts`
- Create: `tests/formula/diagram.test.ts`

**Interfaces:**
- Consumes: `Formula` and `parseFormula(source)` from Task 1; `GraphConstruction`, `emptyGraph`, `declareWire`, `quantifierScope`, `implication`, `atom`, and `finishDiagram` from `src/theories/graph.ts`.
- Produces: `formulaToDiagram(source: string): Diagram` as the only production string-to-diagram entry point; `formulaAstToDiagram(formula: Formula): Diagram` remains module-private.

- [ ] **Step 1: Write failing translation tests**

Use the exact example source. Assert the resulting validated diagram has 22 cut regions, eight atom nodes, and eight quantified wires; inspect head endpoints to prove the unary `Z` wire owns three applications, binary `S` owns one, and unary `P` owns four. Assert existential `z` is scoped directly in the outer implication antecedent, universal wires are scoped in their universal outer cuts, and all application argument wires retain their `IOTA` signature. Add a small structural equivalence test:

```ts
expect(exploreForm(formulaToDiagram('∀ P : i → o. ∀ x. P(x) ⇒ P(x)')))
  .toBe(exploreForm(manuallyBuiltUniversalImplication))
```

where the expected diagram is built independently in the test with `emptyGraph`, `declareWire`, `quantifierScope`, `implication`, `atom`, and `finishDiagram`.

- [ ] **Step 2: Run translation tests and verify they fail**

Run: `npx vitest run --config vitest.config.ts tests/formula/diagram.test.ts`

Expected: FAIL because `src/formula/diagram.ts` does not exist.

- [ ] **Step 3: Implement the total recursive translator**

Implement one recursive function with this interface:

```ts
type TranslationState = {
  readonly graph: GraphConstruction
  readonly bindings: ReadonlyMap<string, WireId>
}

function drawFormula(
  formula: Formula,
  state: TranslationState,
  region: RegionId,
): TranslationState
```

For `atom`, resolve the head and arguments from `bindings` and call `atom`. For `and`, draw left and then right in the same region. For `implies`, call `implication`, draw the left side in `antecedent`, and draw the right side in `consequent`. For a quantifier, call `quantifierScope` with every binder signature, extend a copied bindings map with the returned wires in order, and draw the body in the returned body region. `formulaToDiagram` parses once, translates once from `emptyGraph()`, and returns `finishDiagram(state.graph)`.

- [ ] **Step 4: Export only the authoritative public boundary**

In `src/formula/index.ts`, export `formulaToDiagram`, `parseFormula`, `FormulaError`, and syntax types. Do not export tokenization, the internal type grammar, translation state, or `drawFormula`.

- [ ] **Step 5: Run formula tests, graph tests, and type checking**

Run: `npx vitest run --config vitest.config.ts tests/formula tests/theories/frege-statements.test.ts tests/kernel/diagram/wellformed.test.ts && npm run typecheck`

Expected: all selected tests PASS and TypeScript reports no errors.

- [ ] **Step 6: Commit the translation boundary**

Run:

```bash
git add src/formula/diagram.ts src/formula/index.ts tests/formula/diagram.test.ts
git commit -m "feat: translate formulas into diagrams"
```

Before committing, verify `git diff --cached --name-only` contains exactly those three files.

---

### Task 3: Edit-Mode Formula Submission

**Files:**
- Create: `src/app/formula-entry.ts`
- Create: `tests/app/formula-entry.test.ts`
- Modify: `src/app/shell.ts`
- Modify: `app/style.css`
- Modify: `e2e/app.spec.ts`

**Interfaces:**
- Consumes: `formulaToDiagram(source: string): Diagram` from Task 2 and the shell's existing `pushEdit(diagram)` insertion owner.
- Produces: `mountFormulaEntry(host: HTMLElement, commit: (diagram: Diagram) => void): MountedFormulaEntry`, where `MountedFormulaEntry` exposes `root`, `open()`, `close()`, and `dispose()`.

- [ ] **Step 1: Write failing DOM-component tests**

Create a minimal fake document host. Mount the component, call `open()`, submit `∀ P : i → o. ∀ x : i. P(x)` and assert the provided commit receives a validated diagram and the panel closes. Submit `∀ x. Missing(x)` and assert `.vpa-formula-error` includes a line/column message, the textarea has `aria-invalid="true"`, the panel remains open, and commit was not called. Dispatch `input` after a failure and assert the error and ARIA state clear.

- [ ] **Step 2: Write the failing browser workflow test**

Extend `e2e/app.spec.ts` with the exact example source. In the running app, open `Mode: Edit`, choose `Formula…`, fill `Formula to diagram`, and click `Create diagram`. Assert the debug diagram reports 22 cut regions, eight atoms, and eight wires, and the form is hidden. Reopen the form, submit `∀ x. Missing(x)`, assert the inline error is visible and the debug diagram is unchanged, then press `Ctrl+Z` and assert the original empty diagram is restored.

- [ ] **Step 3: Run the component and browser tests and verify they fail**

Run: `npx vitest run --config vitest.config.ts tests/app/formula-entry.test.ts`

Run: `npx playwright test e2e/app.spec.ts --grep "formula"`

Expected: FAIL because the component and Formula control do not exist.

- [ ] **Step 4: Implement the focused formula-entry component**

In `formula-entry.ts`, construct one initially hidden `<section role="dialog" aria-labelledby="formula-entry-title">` containing a `<form>`, a labeled `<textarea aria-label="Formula to diagram">`, inline `<output class="vpa-formula-error" role="alert">`, `Create diagram`, and `Cancel`. On submit, call `formulaToDiagram(textarea.value)` and only then invoke `commit`; on failure, show the exact error message inline and mark the textarea invalid. Clear field errors on input. Close on success, Cancel, or Escape. Remove every installed listener in `dispose()`.

- [ ] **Step 5: Connect the component to the existing edit owner**

In `shell.ts`, import and mount `mountFormulaEntry(document.body, (diagram) => { requireEdit(); pushEdit(diagram) })`. Add a `Formula…` button to `compass.lifecycle`; show it only when `mode === 'edit'`, close the form when leaving Edit mode or disposing the shell, and include the component's `dispose()` in shell teardown. Do not create another edit state, history array, renderer, or direct engine mutation.

- [ ] **Step 6: Style the form as a responsive fixed panel**

In `app/style.css`, add `.vpa-formula-entry` styling with a fixed centered position below the north compass, `width: min(760px, calc(100vw - 24px))`, readable theme-inheriting textarea, wrapped actions, and a visible error color. Extend the chrome pointer-events selector to include `textarea` and the formula form. Ensure `[hidden]` removes the panel.

- [ ] **Step 7: Run component, browser, and accessibility-focused tests**

Run: `npx vitest run --config vitest.config.ts tests/app/formula-entry.test.ts tests/app/session-history.test.ts tests/app/feedback.test.ts`

Run: `npx playwright test e2e/app.spec.ts --grep "formula"`

Expected: all selected tests PASS; malformed submission does not change the debug diagram and Undo restores the prior edit diagram.

- [ ] **Step 8: Commit the interface integration**

Run:

```bash
git add src/app/formula-entry.ts tests/app/formula-entry.test.ts src/app/shell.ts app/style.css e2e/app.spec.ts
git commit -m "feat: create diagrams from formulas"
```

Before committing, verify `git diff --cached --name-only` contains exactly those five files.

---

### Task 4: Conformance and Full Validation

**Files:**
- Modify: `docs/superpowers/plans/2026-08-03-formula-to-diagram.md` only to check completed steps if desired.
- Modify: `/tmp/vpa-formula-diagram-foundation-20260803-1845.md` outside the repository to append `<conformance>`.

**Interfaces:**
- Consumes: the complete feature and repository validation commands.
- Produces: validation evidence, a clean task-owned Git state, and the completed foundation conformance record.

- [ ] **Step 1: Scan for competing formula translators**

Run: `rg -n "formulaToDiagram|drawFormula|parseFormula" src`

Expected: the parser is defined once, the internal recursive translator is defined once, the public translator is defined once, and the UI imports only the public translator.

- [ ] **Step 2: Run authoritative TypeScript validation**

Run: `npm run typecheck`

Run: `npm run formal:size`

Run: `npx vitest run --config vitest.config.ts --exclude tests/architecture/lean-semantics.test.ts`

If `tests/scripts/emit-theories.test.ts` alone receives `spawnSync npm EPERM` in the sandbox, rerun that exact test outside the sandbox; do not change production code or weaken the test.

Expected: type check, size audit, and every non-in-progress ordinary test PASS.

- [ ] **Step 3: Run complete browser validation**

Run: `npm run e2e`

Expected: every Playwright test PASS, including formula submission, inline refusal, rendered structure, and Undo.

- [ ] **Step 4: Verify unrelated work and task-owned repository state**

Run: `git status --short`

Run: `git diff -- VisualProof/Diagram/Concrete/WirePrimitive/LeavesSemantics.lean docs/goals/primitive-wire-quantifier-lean-completion/state.yaml tests/architecture/lean-semantics.test.ts`

Expected: the three pre-existing files remain modified only by the user and are not staged; no task-owned change remains uncommitted.

- [ ] **Step 5: Append foundation conformance and report commits**

Append a `<conformance>` section recording parser/translator/UI owners, the absence of a displaced formula model, the insertion and rendering surfaces used, validation commands and results, and the `rg` evidence showing there is no competing translation path. Report the task's commit hashes and explicitly distinguish the still-present unrelated Lean worktree modifications.
