# Formula Equality Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let formula source express equality between any two lexically bound variables with the same signature and translate that proposition through the graph identity-node constructor.

**Architecture:** Add equality as an atomic formula variant rather than disguising it as a relation application. The parser will recognize `left = right`, validate both operands against the lexical signature environment, and the translator will attach their existing wires to an identity node; ordinary diagram normalization remains the sole authority for collapsing identities when the one-point rule applies.

**Tech Stack:** TypeScript, Vitest, the existing formula parser, and the existing immutable graph-construction API.

## Global Constraints

- Equality operands must both be lexically bound variables.
- Equality operands must have structurally equal signatures, including relation signatures.
- Translation must use the existing `identity(graph, region, wires)` constructor and retain existing diagram normalization behavior.
- Formula-generated identity nodes must enter the existing compact `identityGeometry` rendering path, with no formula-specific visual representation.
- Preserve the pre-existing changes in `VisualProof/Concrete/Elaboration/SpliceRootCompilation.lean` and `VisualProof/Concrete/Elaboration/SpliceSiteCompilation.lean`.
- Commit only task-owned files after validation.

---

### Task 1: Parse, validate, and draw equality propositions

**Files:**
- Modify: `src/formula/syntax.ts`
- Modify: `src/formula/parse.ts`
- Modify: `src/formula/diagram.ts`
- Test: `tests/formula/parse.test.ts`
- Test: `tests/formula/diagram.test.ts`

**Interfaces:**
- Consumes: `Sig`, `sigEquals(left, right)`, lexical `ReadonlyMap<string, Sig>`, and `identity(graph, region, wires)`.
- Produces: `Formula` variant `{ kind: 'equality'; left: string; right: string; span: SourceSpan }`, parsed from `identifier = identifier` and drawn as an identity-node construction over the corresponding bound wires.

- [x] **Step 1: Write parser tests that define equality syntax and typing**

```ts
it('parses equality between same-signature bound variables', () => {
  const formula = parseFormula('∀ x y. x = y')
  expect(formula.kind).toBe('quantifier')
  if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
  expect(formula.body).toMatchObject({ kind: 'equality', left: 'x', right: 'y' })
})

it('accepts equality at relation signatures and rejects mismatched signatures', () => {
  expect(() => parseFormula('∀ P Q : i → o. P = Q')).not.toThrow()
  expect(() => parseFormula('∀ P : i → o. ∀ x. P = x'))
    .toThrow(/equality operands.*same signature/i)
})
```

- [x] **Step 2: Write translation tests for identity-node output**

```ts
it('draws individual equality as an identity node', () => {
  const diagram = formulaToDiagram('∀ x y. x = y')
  expect(Object.values(diagram.nodes)).toContainEqual({
    kind: 'identity', region: 'r2', sig: IOTA, arity: 2,
  })
})

it('draws equality between relation variables with their shared signature', () => {
  const sig = relSig([IOTA])
  const diagram = formulaToDiagram('∀ P Q : i → o. P = Q')
  expect(Object.values(diagram.nodes)).toContainEqual({
    kind: 'identity', region: 'r2', sig, arity: 2,
  })
})

it('exposes formula equality to the compact identity-node renderer', () => {
  const diagram = formulaToDiagram('∀ x y. x = y')
  const entry = Object.entries(diagram.nodes).find(([, node]) => node.kind === 'identity')
  expect(entry).toBeDefined()
  const engine = mkEngine(diagram, [])
  const body = engine.bodies.get(entry![0])
  expect(body?.kind).toBe('identity')
  expect(body?.geometry).toEqual(identityGeometry(2))
})
```

- [x] **Step 3: Run the focused tests to verify RED**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: FAIL because `=` is rejected by the tokenizer and no equality syntax variant exists.

- [x] **Step 4: Add the immutable equality syntax variant and parser token**

```ts
export type Formula =
  | { readonly kind: 'atom'; readonly name: string; readonly args: readonly string[]; readonly span: SourceSpan }
  | { readonly kind: 'equality'; readonly left: string; readonly right: string; readonly span: SourceSpan }
  | { readonly kind: 'and'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'implies'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'quantifier'; readonly quantifier: 'exists' | 'forall'; readonly binders: readonly FormulaBinder[]; readonly body: Formula; readonly span: SourceSpan }

type TokenKind = 'identifier' | 'forall' | 'exists' | 'implies' | 'and' | '(' | ')' | ',' | ':' | '.' | '=' | 'eof'

// In oneCharacterTokens:
'=': '=',
```

Add a `frozenEquality(left, right, start, end)` constructor. In `parsePrimary`, after consuming the leading identifier, consume `=` and a right-hand identifier before considering relation-application syntax.

- [x] **Step 5: Validate equality operands in the lexical signature environment**

```ts
case 'equality': {
  const left = environment.get(formula.left)
  if (left === undefined) throw new FormulaError(source, formula.span.start, `unbound equality operand '${formula.left}'`)
  const right = environment.get(formula.right)
  if (right === undefined) throw new FormulaError(source, formula.span.start, `unbound equality operand '${formula.right}'`)
  if (!sigEquals(left, right)) {
    throw new FormulaError(source, formula.span.start, 'equality operands must have the same signature')
  }
  return
}
```

- [x] **Step 6: Translate equality with the existing identity constructor**

```ts
case 'equality': {
  const left = boundWire(state.bindings, formula.left)
  const right = boundWire(state.bindings, formula.right)
  return { ...state, graph: identity(state.graph, region, [left, right]).graph }
}
```

- [x] **Step 7: Run focused tests and type checking to verify GREEN**

Run: `npx vitest run --config vitest.config.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts`

Expected: both test files pass.

Run: `npm run typecheck`

Expected: TypeScript reports no errors.

- [x] **Step 8: Run the complete test suite**

Run: `npm test`

Expected: all test files and tests pass.

- [x] **Step 9: Commit the completed feature**

```bash
git add docs/superpowers/plans/2026-08-12-formula-equality.md src/formula/syntax.ts src/formula/parse.ts src/formula/diagram.ts tests/formula/parse.test.ts tests/formula/diagram.test.ts
git commit -m "feat: translate formula equality to identity nodes"
```
