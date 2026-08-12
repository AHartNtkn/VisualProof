# Formula Connectives and Symbol Palette Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Support Unicode negation, disjunction, and biconditional in formula-to-diagram translation and provide accessible insertion buttons for every supported Unicode formula symbol below the source textarea.

**Architecture:** Define one exported Unicode symbol inventory in formula syntax and consume it from both tokenization and the formula-entry palette. Extend the formula AST and precedence parser with `not`, `or`, and `iff`, translate them through cut-based graph constructors, and keep palette insertion as ordinary textarea editing at the current selection.

**Tech Stack:** TypeScript, immutable graph construction, DOM APIs, CSS, Vitest, and Playwright.

## Global Constraints

- Supported Unicode symbols are `∀`, `∃`, `¬`, `∧`, `∨`, `→`, `⇒`, and `↔`.
- Operator precedence is `¬ > ∧ > ∨ > → > ↔`; implication and biconditional are right-associative.
- Negation is one cut, disjunction is `¬(¬A ∧ ¬B)`, and biconditional is `(A → B) ∧ (B → A)`.
- The palette must render immediately below the textarea, replace the current selection, put the caret after the inserted symbol, restore textarea focus, and clear stale validation feedback through the input event.
- Palette controls must be non-submit buttons with accessible names.
- Preserve the existing uncommitted Lean changes and commit only task-owned files.

---

### Task 1: Add connective syntax and authoritative graph translation

**Files:**
- Modify: `src/formula/syntax.ts`
- Modify: `src/formula/parse.ts`
- Modify: `src/formula/index.ts`
- Modify: `src/formula/diagram.ts`
- Modify: `src/theories/graph.ts`
- Test: `tests/formula/parse.test.ts`
- Test: `tests/formula/diagram.test.ts`

**Interfaces:**
- Produces: `FORMULA_UNICODE_SYMBOLS`, `Formula` variants `not`, `or`, and `iff`, `negation(graph, region)`, and `disjunction(graph, region)`.
- Consumes: the existing `biconditional(graph, region)` helper and formula lexical environment.

- [x] **Step 1: Write failing parser tests for symbols and precedence**

```ts
expect(FORMULA_UNICODE_SYMBOLS.map(({ symbol }) => symbol))
  .toEqual(['∀', '∃', '¬', '∧', '∨', '→', '⇒', '↔'])

const formula = parseFormula('∀ A B C D : o. ¬A ∧ B ∨ C → D ↔ A')
expect(formula.kind).toBe('quantifier')
if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
expect(formula.body.kind).toBe('iff')
if (formula.body.kind !== 'iff') throw new Error('expected biconditional')
expect(formula.body.left.kind).toBe('implies')
if (formula.body.left.kind !== 'implies') throw new Error('expected implication')
expect(formula.body.left.left.kind).toBe('or')
if (formula.body.left.left.kind !== 'or') throw new Error('expected disjunction')
expect(formula.body.left.left.left.kind).toBe('and')
if (formula.body.left.left.left.kind !== 'and') throw new Error('expected conjunction')
expect(formula.body.left.left.left.left.kind).toBe('not')
```

- [x] **Step 2: Write failing diagram tests for the three graph encodings**

```ts
const negated = formulaToDiagram('∀ A : o. ¬A')
expect(negated.regions.r3).toEqual({ kind: 'cut', parent: 'r2' })
expect(negated.nodes.n0).toMatchObject({ kind: 'atom', region: 'r3' })

const disjoined = formulaToDiagram('∀ A B : o. A ∨ B')
expect(disjoined.regions.r3).toEqual({ kind: 'cut', parent: 'r2' })
expect(disjoined.regions.r4).toEqual({ kind: 'cut', parent: 'r3' })
expect(disjoined.regions.r5).toEqual({ kind: 'cut', parent: 'r3' })
expect(Object.values(disjoined.nodes).map((node) => node.region)).toEqual(['r4', 'r5'])

const equivalent = formulaToDiagram('∀ A B : o. A ↔ B')
expect(Object.values(equivalent.regions).filter((region) => region.kind === 'cut')).toHaveLength(6)
expect(Object.values(equivalent.nodes).filter((node) => node.kind === 'atom')).toHaveLength(4)
```

- [x] **Step 3: Run focused formula tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: FAIL because `¬`, `∨`, and `↔` are rejected and their AST variants do not exist.

- [x] **Step 4: Define the shared symbol inventory and AST variants**

```ts
export type FormulaUnicodeTokenKind =
  | 'forall' | 'exists' | 'not' | 'and' | 'or' | 'implies' | 'iff'

export const FORMULA_UNICODE_SYMBOLS = Object.freeze([
  { symbol: '∀', label: 'Universal quantifier', token: 'forall' },
  { symbol: '∃', label: 'Existential quantifier', token: 'exists' },
  { symbol: '¬', label: 'Negation', token: 'not' },
  { symbol: '∧', label: 'Conjunction', token: 'and' },
  { symbol: '∨', label: 'Disjunction', token: 'or' },
  { symbol: '→', label: 'Implication', token: 'implies' },
  { symbol: '⇒', label: 'Alternative implication', token: 'implies' },
  { symbol: '↔', label: 'Biconditional', token: 'iff' },
] satisfies readonly {
  readonly symbol: string
  readonly label: string
  readonly token: FormulaUnicodeTokenKind
}[])

export type Formula =
  | { readonly kind: 'atom'; readonly name: string; readonly args: readonly string[]; readonly span: SourceSpan }
  | { readonly kind: 'equality'; readonly operands: readonly [string, string, ...string[]]; readonly span: SourceSpan }
  | { readonly kind: 'not'; readonly body: Formula; readonly span: SourceSpan }
  | { readonly kind: 'and'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'or'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'implies'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'iff'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'quantifier'; readonly quantifier: 'exists' | 'forall'; readonly binders: readonly FormulaBinder[]; readonly body: Formula; readonly span: SourceSpan }
```

- [x] **Step 5: Implement tokenization and the precedence parser**

Use `FORMULA_UNICODE_SYMBOLS.find(({ symbol }) => symbol === character)` for Unicode tokens. Implement `parseBiconditional`, `parseImplication`, `parseDisjunction`, `parseConjunction`, and recursive `parseUnary`, with parenthesized and quantified bodies calling `parseBiconditional`.

```ts
function parseBiconditional(): Formula {
  const left = parseImplication()
  if (peek().kind !== 'iff') return left
  take()
  return frozenBinary('iff', left, parseBiconditional())
}

function parseDisjunction(): Formula {
  let formula = parseConjunction()
  while (peek().kind === 'or') {
    take()
    formula = frozenBinary('or', formula, parseConjunction())
  }
  return formula
}

function parseUnary(): Formula {
  const token = peek()
  if (token.kind !== 'not') return parsePrimary()
  take()
  const body = parseUnary()
  return Object.freeze({ kind: 'not', body, span: frozenSpan(token.start, body.span.end) })
}
```

- [x] **Step 6: Add cut-based graph constructors and translation cases**

```ts
export function negation(graph: GraphConstruction, region: RegionId): GraphResult<RegionId> {
  return addCut(graph, region)
}

export function disjunction(
  graph: GraphConstruction,
  region: RegionId,
): GraphResult<{ readonly left: RegionId; readonly right: RegionId }> {
  const outer = addCut(graph, region)
  const left = addCut(outer.graph, outer.value)
  const right = addCut(left.graph, outer.value)
  return result(right.graph, Object.freeze({ left: left.value, right: right.value }))
}
```

```ts
case 'not': {
  const scope = negation(state.graph, region)
  return drawFormula(formula.body, { ...state, graph: scope.graph }, scope.value)
}
case 'or': {
  const scope = disjunction(state.graph, region)
  const left = drawFormula(formula.left, { ...state, graph: scope.graph }, scope.value.left)
  return drawFormula(formula.right, left, scope.value.right)
}
case 'iff': {
  const scope = biconditional(state.graph, region)
  const forwardLeft = drawFormula(formula.left, { ...state, graph: scope.graph }, scope.value.forward.antecedent)
  const forwardRight = drawFormula(formula.right, forwardLeft, scope.value.forward.consequent)
  const reverseRight = drawFormula(formula.right, forwardRight, scope.value.reverse.antecedent)
  return drawFormula(formula.left, reverseRight, scope.value.reverse.consequent)
}
```

- [x] **Step 7: Run focused formula tests and type checking**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: both test files pass.

Run: `npm run typecheck`

Expected: no TypeScript errors.

### Task 2: Render and operate the shared Unicode symbol palette

**Files:**
- Modify: `src/app/formula-entry.ts`
- Modify: `app/style.css`
- Test: `tests/app/formula-entry.test.ts`
- Test: `e2e/app.spec.ts`

**Interfaces:**
- Consumes: `FORMULA_UNICODE_SYMBOLS` from the formula package.
- Produces: `.vpa-formula-symbols`, an accessible button group immediately after the textarea.

- [x] **Step 1: Write failing DOM tests for palette contents and insertion**

```ts
expect(symbols.children.map((button) => button.textContent))
  .toEqual(['∀', '∃', '¬', '∧', '∨', '→', '⇒', '↔'])
expect(symbols.children.every((button) => button.type === 'button')).toBe(true)
expect(form.children.indexOf(symbols)).toBe(form.children.indexOf(textarea) + 1)

textarea.value = 'AB'
textarea.setSelectionRange(1, 1)
symbols.children[4]!.dispatchEvent(new Event('click'))
expect(textarea.value).toBe('A∨B')
expect(textarea.selectionStart).toBe(2)
expect(textarea.selectionEnd).toBe(2)
expect(documentDouble.activeElement).toBe(textarea)
```

- [x] **Step 2: Run the formula-entry unit test to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/app/formula-entry.test.ts`

Expected: FAIL because `.vpa-formula-symbols` does not exist.

- [x] **Step 3: Render palette buttons from the shared inventory**

```ts
const symbols = document.createElement('div')
symbols.className = 'vpa-formula-symbols'
symbols.setAttribute('role', 'group')
symbols.setAttribute('aria-label', 'Formula symbols')
const symbolButtons = FORMULA_UNICODE_SYMBOLS.map(({ symbol, label }) => {
  const button = document.createElement('button')
  button.type = 'button'
  button.textContent = symbol
  button.setAttribute('aria-label', label)
  button.setAttribute('title', label)
  symbols.append(button)
  return { button, symbol }
})

const symbolHandlers = symbolButtons.map(({ button, symbol }) => {
  const handler = (): void => {
    const start = textarea.selectionStart
    const end = textarea.selectionEnd
    textarea.value = textarea.value.slice(0, start) + symbol + textarea.value.slice(end)
    const caret = start + symbol.length
    textarea.setSelectionRange(caret, caret)
    textarea.dispatchEvent(new Event('input', { bubbles: true }))
    textarea.focus()
  }
  button.addEventListener('click', handler)
  return { button, handler }
})
```

Append `symbols` immediately after `textarea`, and remove every `symbolHandlers` click listener during `dispose()`.

- [x] **Step 4: Style the palette as a compact row below the textarea**

```css
.vpa-formula-symbols { display: flex; flex-wrap: wrap; gap: 6px; }
.vpa-formula-symbols button { min-width: 34px; border: 1px solid var(--vpa-control-border); border-radius: 7px; padding: 3px 8px; background: var(--vpa-control-surface); color: var(--vpa-control-foreground); font-size: 17px; cursor: pointer; }
.vpa-formula-symbols button:hover { background: var(--vpa-control-hover-surface); }
.vpa-formula-symbols button:active { background: var(--vpa-control-active-surface); }
.vpa-formula-symbols button:focus-visible { outline: 2px solid var(--vpa-control-focus-ring); outline-offset: 2px; }
```

- [x] **Step 5: Add browser validation for ordering, position, and caret insertion**

```ts
test('formula symbol palette sits below the source and inserts at the caret', async ({ page }) => {
  await page.goto('/?debug')
  await page.getByRole('button', { name: /Mode: Edit/u }).click()
  await page.getByRole('button', { name: 'Formula…', exact: true }).click()
  const dialog = page.getByRole('dialog')
  const source = dialog.getByLabel('Formula to diagram')
  const palette = dialog.getByRole('group', { name: 'Formula symbols' })
  await expect(palette.getByRole('button')).toHaveText(['∀', '∃', '¬', '∧', '∨', '→', '⇒', '↔'])
  const sourceBox = await source.boundingBox()
  const paletteBox = await palette.boundingBox()
  if (sourceBox === null || paletteBox === null) throw new Error('formula controls must have layout boxes')
  expect(paletteBox.y).toBeGreaterThanOrEqual(sourceBox.y + sourceBox.height)
  await source.fill('AB')
  await source.evaluate((element) => (element as HTMLTextAreaElement).setSelectionRange(1, 1))
  await palette.getByRole('button', { name: 'Disjunction' }).click()
  await expect(source).toHaveValue('A∨B')
  await expect(source).toBeFocused()
})
```

- [x] **Step 6: Run focused app and browser tests**

Run: `npx vitest run --config vitest.config.ts tests/app/formula-entry.test.ts`

Expected: PASS.

Run: `npx playwright test e2e/app.spec.ts --grep "formula symbol palette"`

Expected: PASS.

- [x] **Step 7: Run complete validation**

Run: `npm run typecheck`

Expected: no TypeScript errors.

Run: `npm test`

Expected: all test files and tests pass.

- [x] **Step 8: Commit the completed feature**

```bash
git add docs/superpowers/plans/2026-08-12-formula-connectives-and-symbol-palette.md src/formula/syntax.ts src/formula/parse.ts src/formula/index.ts src/formula/diagram.ts src/theories/graph.ts src/app/formula-entry.ts app/style.css tests/formula/parse.test.ts tests/formula/diagram.test.ts tests/app/formula-entry.test.ts e2e/app.spec.ts
git commit -m "feat: add formula connectives and symbol palette"
```
