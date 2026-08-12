# Chained Formula Equality Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make equality chains such as `x = y = z` generate one multi-port identity node.

**Architecture:** Replace the binary equality AST fields with one immutable operand list used by both two-variable and chained equalities. Parse one-or-more `= identifier` suffixes into that list, validate every operand against the first operand's signature, and pass all corresponding wires to the existing n-ary identity constructor and compact renderer.

**Tech Stack:** TypeScript, Vitest, the formula parser, immutable graph construction, and identity-node view geometry.

## Global Constraints

- A chain must contain at least two lexically bound variable operands.
- Every operand in a chain must have the same structural signature.
- One equality chain must produce one identity node whose arity equals the operand count.
- Binary equality must use the same operand-list representation and translation path.
- Formula-generated identity nodes must continue to use the existing compact `identityGeometry` rendering path.
- Preserve the existing uncommitted Lean changes and commit only task-owned files.

---

### Task 1: Replace binary equality with n-ary equality chains

**Files:**
- Create: `docs/superpowers/plans/2026-08-12-chained-formula-equality.md`
- Modify: `src/formula/syntax.ts`
- Modify: `src/formula/parse.ts`
- Modify: `src/formula/diagram.ts`
- Modify: `tests/formula/parse.test.ts`
- Modify: `tests/formula/diagram.test.ts`

**Interfaces:**
- Consumes: lexical `ReadonlyMap<string, Sig>`, `sigEquals(left, right)`, `boundWire(bindings, name)`, `identity(graph, region, wires)`, and `identityGeometry(arity)`.
- Produces: `Formula` variant `{ kind: 'equality'; operands: readonly [string, string, ...string[]]; span: SourceSpan }`, whose tuple type requires at least two operands and which translates to exactly one identity construction with the same arity.

- [x] **Step 1: Write failing parser tests for one canonical operand list**

```ts
function expectEquality(formula: Formula, operands: readonly string[]): void {
  expect(formula.kind).toBe('equality')
  if (formula.kind !== 'equality') throw new Error('expected equality')
  expect(formula.operands).toEqual(operands)
  expect(Object.isFrozen(formula.operands)).toBe(true)
}

it('parses chained equality into one immutable operand list', () => {
  const formula = parseFormula('∀ x y z. x = y = z')
  expect(formula.kind).toBe('quantifier')
  if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
  expectEquality(formula.body, ['x', 'y', 'z'])
})

it('rejects a signature mismatch anywhere in an equality chain', () => {
  expect(() => parseFormula('∀ P Q : i → o. ∀ x. P = Q = x'))
    .toThrow(/equality operands must have the same signature/i)
})
```

- [x] **Step 2: Write failing translation and rendering tests for arity three**

```ts
it('draws an equality chain as one compact multi-port identity node', () => {
  const diagram = formulaToDiagram('∀ x y z. x = y = z')
  const entries = Object.entries(diagram.nodes).filter(([, node]) => node.kind === 'identity')
  expect(entries).toHaveLength(1)
  expect(entries[0]![1]).toEqual({
    kind: 'identity', region: 'r2', sig: IOTA, arity: 3,
  })
  const body = mkEngine(diagram, []).bodies.get(entries[0]![0])
  expect(body?.geometry).toEqual(identityGeometry(3))
})
```

- [x] **Step 3: Run focused tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: FAIL because the parser leaves the second `=` as an unexpected trailing token and the equality AST exposes binary fields.

- [x] **Step 4: Replace the binary AST and frozen constructor**

```ts
export type Formula =
  | { readonly kind: 'atom'; readonly name: string; readonly args: readonly string[]; readonly span: SourceSpan }
  | { readonly kind: 'equality'; readonly operands: readonly [string, string, ...string[]]; readonly span: SourceSpan }
  | { readonly kind: 'and'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'implies'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'quantifier'; readonly quantifier: 'exists' | 'forall'; readonly binders: readonly FormulaBinder[]; readonly body: Formula; readonly span: SourceSpan }

function frozenEquality(
  operands: readonly [string, string, ...string[]],
  start: number,
  end: number,
): Formula {
  const frozenOperands: readonly [string, string, ...string[]] = Object.freeze([
    operands[0],
    operands[1],
    ...operands.slice(2),
  ])
  return Object.freeze({
    kind: 'equality',
    operands: frozenOperands,
    span: frozenSpan(start, end),
  })
}
```

- [x] **Step 5: Parse and validate every equality operand**

```ts
take()
const right = expect('identifier', 'an equality operand')
const operands: [string, string, ...string[]] = [head.text, right.text]
let end = right.end
while (peek().kind === '=') {
  take()
  const operand = expect('identifier', 'an equality operand')
  operands.push(operand.text)
  end = operand.end
}
return frozenEquality(operands, head.start, end)

case 'equality': {
  const [firstName, ...remainingNames] = formula.operands
  const first = environment.get(firstName)
  if (first === undefined) {
    throw new FormulaError(source, formula.span.start, `unbound equality operand '${firstName}'`)
  }
  for (const name of remainingNames) {
    const candidate = environment.get(name)
    if (candidate === undefined) {
      throw new FormulaError(source, formula.span.start, `unbound equality operand '${name}'`)
    }
    if (!sigEquals(first, candidate)) {
      throw new FormulaError(source, formula.span.start, 'equality operands must have the same signature')
    }
  }
  return
}
```

- [x] **Step 6: Translate the complete chain through one identity constructor call**

```ts
case 'equality': {
  const wires = formula.operands.map((name) => boundWire(state.bindings, name))
  return { ...state, graph: identity(state.graph, region, wires).graph }
}
```

- [x] **Step 7: Run focused tests and type checking**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: both files pass, including binary and chained equality.

Run: `npm run typecheck`

Expected: no TypeScript errors.

- [x] **Step 8: Run complete validation**

Run: `npm test`

Expected: all test files and tests pass.

- [x] **Step 9: Commit the completed feature**

```bash
git add docs/superpowers/plans/2026-08-12-chained-formula-equality.md src/formula/syntax.ts src/formula/parse.ts src/formula/diagram.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts
git commit -m "feat: support chained formula equality"
```
