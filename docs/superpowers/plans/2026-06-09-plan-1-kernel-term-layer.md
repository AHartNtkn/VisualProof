# Kernel Term Layer Implementation Plan (Plan 1 of 6)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The pure, headless λ-term core of the kernel: de Bruijn terms, ASCII parser/printer, βη reduction with explicit fuel, reduction-path certificates, convertibility checking, and stable term serialization.

**Architecture:** Spec: `docs/superpowers/specs/2026-06-09-visual-proof-assistant-design.md` (§2.2 term grammar, §3.7 deduction modulo, §4.3–4.4). Pure TypeScript under `src/kernel/term/`, zero DOM imports, immutable values, every function deterministic. Normal-order β-reduction (finds a normal form whenever one exists) followed by η-contraction to fixpoint (complete for βη-normal forms by η-postponement). Constants are opaque at this layer — unfolding is rule 7, owned by later plans.

**Tech Stack:** TypeScript (strict), Vitest, Node ≥ 20. No runtime dependencies.

**Plan sequence** (each plan ships working, tested software; later plans are written once their predecessors' real types exist):

1. **This plan** — kernel term layer.
2. Diagram syntax: regions/nodes/wires/atoms, well-formedness, canonicalization + fingerprints.
3. Foundational primitives 1–8, polarity, matching modulo βη.
4. Derived rules, proof objects, bidirectional construction + replay, theory store + file format.
5. Deterministic layout + physics simulation + rendering (Tromp bending, visual language).
6. App shell, interaction modes, persistence UI, bundled examples, end-to-end tests.

---

### Task 1: Project scaffold

**Files:**
- Create: `package.json`
- Create: `tsconfig.json`
- Create: `vitest.config.ts`
- Create: `tests/kernel/term/smoke.test.ts`

- [ ] **Step 1: Write package.json**

```json
{
  "name": "visual-proof-assistant",
  "private": true,
  "version": "0.1.0",
  "type": "module",
  "engines": { "node": ">=20" },
  "scripts": {
    "test": "vitest run",
    "test:watch": "vitest",
    "typecheck": "tsc --noEmit"
  },
  "devDependencies": {
    "typescript": "^5.5.0",
    "vitest": "^2.0.0"
  }
}
```

- [ ] **Step 2: Write tsconfig.json**

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "module": "ES2022",
    "moduleResolution": "bundler",
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "exactOptionalPropertyTypes": true,
    "noFallthroughCasesInSwitch": true,
    "forceConsistentCasingInFileNames": true,
    "skipLibCheck": true,
    "isolatedModules": true,
    "verbatimModuleSyntax": true,
    "noUnusedLocals": true,
    "noUnusedParameters": true,
    "noImplicitReturns": true,
    "types": []
  },
  "include": ["src", "tests"]
}
```

- [ ] **Step 3: Write vitest.config.ts**

```ts
import { defineConfig } from 'vitest/config'

export default defineConfig({
  test: {
    include: ['tests/**/*.test.ts'],
  },
})
```

- [ ] **Step 4: Write smoke test**

`tests/kernel/term/smoke.test.ts`:

```ts
import { describe, it, expect } from 'vitest'

describe('scaffold', () => {
  it('runs tests', () => {
    expect(1 + 1).toBe(2)
  })
})
```

- [ ] **Step 5: Install and verify**

Run: `npm install && npm test`
Expected: 1 test file, 1 passed.

Run: `npm run typecheck`
Expected: exit 0, no output.

- [ ] **Step 6: Commit**

```bash
git add package.json package-lock.json tsconfig.json vitest.config.ts tests/kernel/term/smoke.test.ts
git commit -m "chore: scaffold TypeScript + Vitest project"
```

---

### Task 2: Term type, constructors, equality, free ports

**Files:**
- Create: `src/kernel/term/term.ts`
- Test: `tests/kernel/term/term.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/term.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app, termEq, freePorts } from '../../../src/kernel/term/term'

describe('term constructors and equality', () => {
  it('structural equality is alpha-equality because binders are de Bruijn', () => {
    // \x. x  and  \y. y  are the same term: lam(bvar(0))
    const id1 = lam(bvar(0))
    const id2 = lam(bvar(0))
    expect(termEq(id1, id2), 'identical structure must be equal').toBe(true)
  })

  it('distinguishes structurally different terms', () => {
    expect(termEq(lam(bvar(0)), lam(lam(bvar(0))))).toBe(false)
    expect(termEq(port('y'), port('z'))).toBe(false)
    expect(termEq(cnst('plus'), port('plus'))).toBe(false)
    expect(termEq(app(port('f'), port('a')), app(port('a'), port('f')))).toBe(false)
  })

  it('rejects negative de Bruijn indices at construction', () => {
    expect(() => bvar(-1)).toThrowError(/negative/i)
  })

  it('rejects fractional de Bruijn indices at construction', () => {
    expect(() => bvar(0.5)).toThrowError(/fractional/i)
  })

  it('rejects unsafely large de Bruijn indices at construction', () => {
    expect(() => bvar(2 ** 53)).toThrowError(/safe integer/i)
  })

  it('rejects empty port and const names at construction', () => {
    expect(() => port('')).toThrowError(/non-empty/i)
    expect(() => cnst('')).toThrowError(/non-empty/i)
  })

  it('is reflexive on compound terms', () => {
    const t = app(cnst('plus'), port('m'))
    expect(termEq(t, t)).toBe(true)
  })
})

describe('freePorts', () => {
  it('returns ports in first-occurrence order (fn before arg, outside-in)', () => {
    // \x. y (z y x) — first occurrences: y, then z
    const t = lam(app(port('y'), app(app(port('z'), port('y')), bvar(0))))
    expect(freePorts(t)).toEqual(['y', 'z'])
  })

  it('returns empty list for closed terms', () => {
    const churchTwo = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(freePorts(churchTwo)).toEqual([])
  })

  it('does not count constants as ports', () => {
    const t = app(cnst('plus'), port('m'))
    expect(freePorts(t)).toEqual(['m'])
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/term.test.ts`
Expected: FAIL — cannot resolve `../../../src/kernel/term/term`.

- [ ] **Step 3: Implement**

`src/kernel/term/term.ts`:

```ts
export type Term =
  | { readonly kind: 'bvar'; readonly index: number }
  | { readonly kind: 'port'; readonly name: string }
  | { readonly kind: 'const'; readonly id: string }
  | { readonly kind: 'lam'; readonly body: Term }
  | { readonly kind: 'app'; readonly fn: Term; readonly arg: Term }

export function bvar(index: number): Term {
  if (!Number.isSafeInteger(index) || index < 0) {
    throw new Error(`bvar index must be a non-negative safe integer, got ${index} (negative, fractional, or unsafely large indices are meaningless)`)
  }
  return { kind: 'bvar', index }
}

export function port(name: string): Term {
  if (name.length === 0) throw new Error('port name must be non-empty')
  return { kind: 'port', name }
}

export function cnst(id: string): Term {
  if (id.length === 0) throw new Error('const id must be non-empty')
  return { kind: 'const', id }
}

export function lam(body: Term): Term {
  return { kind: 'lam', body }
}

export function app(fn: Term, arg: Term): Term {
  return { kind: 'app', fn, arg }
}

export function termEq(a: Term, b: Term): boolean {
  if (a.kind !== b.kind) return false
  switch (a.kind) {
    case 'bvar': return a.index === (b as Extract<Term, { kind: 'bvar' }>).index
    case 'port': return a.name === (b as Extract<Term, { kind: 'port' }>).name
    case 'const': return a.id === (b as Extract<Term, { kind: 'const' }>).id
    case 'lam': return termEq(a.body, (b as Extract<Term, { kind: 'lam' }>).body)
    case 'app': {
      const bb = b as Extract<Term, { kind: 'app' }>
      return termEq(a.fn, bb.fn) && termEq(a.arg, bb.arg)
    }
  }
}

/** Free ports in first-occurrence order: lam descends into body; app visits fn, then arg. */
export function freePorts(t: Term): string[] {
  const seen = new Set<string>()
  const order: string[] = []
  const visit = (u: Term): void => {
    switch (u.kind) {
      case 'port':
        if (!seen.has(u.name)) { seen.add(u.name); order.push(u.name) }
        return
      case 'lam': visit(u.body); return
      case 'app': visit(u.fn); visit(u.arg); return
      case 'bvar':
      case 'const':
        return
    }
  }
  visit(t)
  return order
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/term.test.ts`
Expected: PASS (all tests). Also run `npm run typecheck` — exit 0.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/term.ts tests/kernel/term/term.test.ts
git commit -m "feat(kernel): de Bruijn term type, constructors, equality, freePorts"
```

---

### Task 3: Printer

**Files:**
- Create: `src/kernel/term/print.ts`
- Test: `tests/kernel/term/print.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/print.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app } from '../../../src/kernel/term/term'
import { printTerm } from '../../../src/kernel/term/print'

describe('printTerm', () => {
  it('prints identity', () => {
    expect(printTerm(lam(bvar(0)))).toBe('\\x0. x0')
  })

  it('prints Church two with nested binders named outside-in', () => {
    const churchTwo = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(printTerm(churchTwo)).toBe('\\x0. \\x1. x0 (x0 x1)')
  })

  it('prints application left-associatively without redundant parens', () => {
    const t = app(app(port('f'), port('a')), port('b'))
    expect(printTerm(t)).toBe('f a b')
  })

  it('parenthesizes argument applications and lambda operands', () => {
    expect(printTerm(app(port('f'), app(port('g'), port('a'))))).toBe('f (g a)')
    expect(printTerm(app(lam(bvar(0)), port('a')))).toBe('(\\x0. x0) a')
    expect(printTerm(app(port('f'), lam(bvar(0))))).toBe('f (\\x0. x0)')
  })

  it('prints ports and constants by name', () => {
    expect(printTerm(app(cnst('plus'), port('m')))).toBe('plus m')
  })

  it('avoids capture-looking collisions with port names by prefixing underscores', () => {
    // port literally named x0 — binder must not print as x0
    const t = lam(app(bvar(0), port('x0')))
    expect(printTerm(t)).toBe('\\_x0. _x0 x0')
  })

  it('throws on unbound de Bruijn index', () => {
    expect(() => printTerm(bvar(0))).toThrowError(/unbound de Bruijn index 0/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/print.test.ts`
Expected: FAIL — cannot resolve `print`.

- [ ] **Step 3: Implement**

`src/kernel/term/print.ts`:

```ts
import type { Term } from './term'
import { freePorts } from './term'

/**
 * Deterministic printer. Binder at nesting depth d (outermost = 0) is named
 * `x{d}`, prefixed with underscores until it collides with no port name,
 * constant id, or other binder name in the term. ASCII `\` for lambda.
 */
export function printTerm(t: Term): string {
  const taken = new Set<string>(freePorts(t))
  collectConsts(t, taken)
  return go(t, [], taken, 'top')
}

function collectConsts(t: Term, out: Set<string>): void {
  switch (t.kind) {
    case 'const': out.add(t.id); return
    case 'lam': collectConsts(t.body, out); return
    case 'app': collectConsts(t.fn, out); collectConsts(t.arg, out); return
    case 'bvar':
    case 'port':
      return
  }
}

type Ctx = 'top' | 'appFn' | 'appArg'

function go(t: Term, env: string[], taken: Set<string>, ctx: Ctx): string {
  switch (t.kind) {
    case 'bvar': {
      const name = env[env.length - 1 - t.index]
      if (name === undefined) {
        throw new Error(`unbound de Bruijn index ${t.index} at depth ${env.length}; term is malformed`)
      }
      return name
    }
    case 'port': return t.name
    case 'const': return t.id
    case 'lam': {
      let name = `x${env.length}`
      // env.includes guards a prefix expansion of `x{d}` colliding with an outer
      // binder's chosen name; unreachable under the current scheme (different
      // depths produce different numeric suffixes) but kept as a safety net.
      while (taken.has(name) || env.includes(name)) name = `_${name}`
      const body = go(t.body, [...env, name], taken, 'top')
      const s = `\\${name}. ${body}`
      return ctx === 'top' ? s : `(${s})`
    }
    case 'app': {
      const fn = go(t.fn, env, taken, 'appFn')
      const arg = go(t.arg, env, taken, 'appArg')
      const s = `${fn} ${arg}`
      return ctx === 'appArg' ? `(${s})` : s
    }
  }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/print.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/print.ts tests/kernel/term/print.test.ts
git commit -m "feat(kernel): deterministic ASCII term printer"
```

---

### Task 4: Parser

**Files:**
- Create: `src/kernel/term/parse.ts`
- Test: `tests/kernel/term/parse.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/parse.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app, termEq } from '../../../src/kernel/term/term'
import { parseTerm, ParseError } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'

const consts = new Set(['plus', 'one'])

describe('parseTerm', () => {
  it('parses identity with \\ for lambda', () => {
    expect(termEq(parseTerm('\\x. x', consts), lam(bvar(0)))).toBe(true)
  })

  it('parses Church two', () => {
    const expected = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(termEq(parseTerm('\\f. \\x. f (f x)', consts), expected)).toBe(true)
  })

  it('supports multi-binder sugar \\x y. e', () => {
    expect(termEq(parseTerm('\\f x. f x', consts), parseTerm('\\f. \\x. f x', consts))).toBe(true)
  })

  it('application is left-associative and binds tighter than lambda body', () => {
    expect(termEq(parseTerm('f a b', consts), app(app(port('f'), port('a')), port('b')))).toBe(true)
    expect(termEq(parseTerm('\\x. f x x', consts), lam(app(app(port('f'), bvar(0)), bvar(0))))).toBe(true)
  })

  it('treats a lambda in argument position as the final argument extending to the end', () => {
    expect(termEq(parseTerm('f \\x. x', consts), app(port('f'), lam(bvar(0))))).toBe(true)
    expect(termEq(parseTerm('f g \\x. x', consts), app(app(port('f'), port('g')), lam(bvar(0))))).toBe(true)
    expect(termEq(parseTerm('\\x. f \\y. y', consts), lam(app(port('f'), lam(bvar(0)))))).toBe(true)
  })

  it('rejects duplicate binder names within one binder group', () => {
    expect(() => parseTerm('\\x x. x', consts)).toThrowError(/duplicate binder name 'x'/i)
    // shadowing across nested lambdas remains legal (covered elsewhere): \x. \x. x
  })

  it('rejects unexpected characters with positions', () => {
    expect(() => parseTerm('f α g', consts)).toThrowError(ParseError)
    expect(() => parseTerm('f 0 g', consts)).toThrowError(/unexpected character '0'/i)
  })

  it('resolves names: bound > const > port; inner binders shadow outer', () => {
    expect(termEq(parseTerm('plus one y', consts), app(app(cnst('plus'), cnst('one')), port('y')))).toBe(true)
    // bound name shadows a constant
    expect(termEq(parseTerm('\\plus. plus', consts), lam(bvar(0)))).toBe(true)
    // inner x shadows outer x
    expect(termEq(parseTerm('\\x. \\x. x', consts), lam(lam(bvar(0))))).toBe(true)
  })

  it('round-trips with the printer', () => {
    const src = '\\x0. \\x1. x0 (x0 x1)'
    expect(printTerm(parseTerm(src, consts))).toBe(src)
    const withNames = 'plus m (\\x0. x0)'
    expect(printTerm(parseTerm(withNames, consts))).toBe(withNames)
  })

  it('rejects empty input, unbalanced parens, and stray dots with positions', () => {
    expect(() => parseTerm('', consts)).toThrowError(ParseError)
    expect(() => parseTerm('(f a', consts)).toThrowError(/expected '\)'.*position 4/i)
    expect(() => parseTerm('f . a', consts)).toThrowError(/unexpected '\.'/i)
    expect(() => parseTerm('\\. x', consts)).toThrowError(/expected binder name/i)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/parse.test.ts`
Expected: FAIL — cannot resolve `parse`.

- [ ] **Step 3: Implement**

`src/kernel/term/parse.ts`:

```ts
import type { Term } from './term'
import { bvar, port, cnst, lam, app } from './term'

export class ParseError extends Error {
  constructor(message: string, readonly position: number) {
    super(`${message} at position ${position}`)
    this.name = 'ParseError'
  }
}

type Token =
  | { kind: 'lambda'; pos: number }
  | { kind: 'dot'; pos: number }
  | { kind: 'lparen'; pos: number }
  | { kind: 'rparen'; pos: number }
  | { kind: 'ident'; name: string; pos: number }

const IDENT_START = /[A-Za-z_]/
const IDENT_CONT = /[A-Za-z0-9_']/

function tokenize(src: string): Token[] {
  const out: Token[] = []
  let i = 0
  while (i < src.length) {
    const c = src[i]!
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r') { i++; continue }
    if (c === '\\') { out.push({ kind: 'lambda', pos: i }); i++; continue }
    if (c === '.') { out.push({ kind: 'dot', pos: i }); i++; continue }
    if (c === '(') { out.push({ kind: 'lparen', pos: i }); i++; continue }
    if (c === ')') { out.push({ kind: 'rparen', pos: i }); i++; continue }
    if (IDENT_START.test(c)) {
      const start = i
      while (i < src.length && IDENT_CONT.test(src[i]!)) i++
      out.push({ kind: 'ident', name: src.slice(start, i), pos: start })
      continue
    }
    throw new ParseError(`unexpected character '${c}'`, i)
  }
  return out
}

/**
 * Grammar:
 *   term   := lambda | appSeq
 *   lambda := '\' ident+ '.' term
 *   appSeq := atom atom*            (left-associative)
 *   atom   := ident | '(' term ')'
 * Name resolution: innermost binder first, then constants, then port.
 */
export function parseTerm(src: string, constIds: ReadonlySet<string>): Term {
  const tokens = tokenize(src)
  if (tokens.length === 0) throw new ParseError('empty input', 0)
  let i = 0

  const peek = (): Token | undefined => tokens[i]
  const endPos = (): number => {
    const last = tokens[tokens.length - 1]!
    return last.kind === 'ident' ? last.pos + last.name.length : last.pos + 1
  }

  function parseTermAt(env: string[]): Term {
    const t = peek()
    if (t !== undefined && t.kind === 'lambda') {
      i++
      const names: string[] = []
      for (;;) {
        const tok = peek()
        if (tok === undefined || tok.kind !== 'ident') break
        if (names.includes(tok.name)) {
          throw new ParseError(`duplicate binder name '${tok.name}' in binder group`, tok.pos)
        }
        names.push(tok.name)
        i++
      }
      if (names.length === 0) {
        throw new ParseError("expected binder name after '\\'", peek()?.pos ?? endPos())
      }
      const dot = peek()
      if (dot === undefined || dot.kind !== 'dot') {
        throw new ParseError("expected '.' after binder names", dot?.pos ?? endPos())
      }
      i++
      let body = parseTermAt([...env, ...names])
      for (let k = 0; k < names.length; k++) body = lam(body)
      return body
    }
    return parseAppSeq(env)
  }

  function parseAppSeq(env: string[]): Term {
    let t = parseAtom(env)
    for (;;) {
      const nxt = peek()
      if (nxt === undefined || nxt.kind === 'dot' || nxt.kind === 'rparen') break
      if (nxt.kind === 'lambda') {
        // '\' in argument position: standard λ-calculus convention (as in Haskell/ML) —
        // the lambda is the final argument and its body extends to the end of the expression.
        t = app(t, parseTermAt(env))
        break
      }
      t = app(t, parseAtom(env))
    }
    return t
  }

  function parseAtom(env: string[]): Term {
    const t = peek()
    if (t === undefined) throw new ParseError('unexpected end of input', endPos())
    if (t.kind === 'ident') {
      i++
      const idx = env.lastIndexOf(t.name)
      if (idx >= 0) return bvar(env.length - 1 - idx)
      if (constIds.has(t.name)) return cnst(t.name)
      return port(t.name)
    }
    if (t.kind === 'lparen') {
      i++
      const inner = parseTermAt(env)
      const close = peek()
      if (close === undefined || close.kind !== 'rparen') {
        throw new ParseError("expected ')'", close?.pos ?? endPos())
      }
      i++
      return inner
    }
    if (t.kind === 'dot') throw new ParseError("unexpected '.'", t.pos)
    throw new ParseError(`unexpected '${t.kind === 'rparen' ? ')' : '\\'}'`, t.pos)
  }

  const result = parseTermAt([])
  const leftover = peek()
  if (leftover !== undefined) {
    throw new ParseError(`unexpected '${tokenDisplay(leftover)}'`, leftover.pos)
  }
  return result
}

function tokenDisplay(t: Token): string {
  switch (t.kind) {
    case 'ident': return t.name
    case 'dot': return '.'
    case 'lparen': return '('
    case 'rparen': return ')'
    case 'lambda': return '\\'
  }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/parse.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/parse.ts tests/kernel/term/parse.test.ts
git commit -m "feat(kernel): ASCII lambda parser with positions and name resolution"
```

---

### Task 5: Shift and substitution

**Files:**
- Create: `src/kernel/term/reduce.ts`
- Test: `tests/kernel/term/reduce.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/reduce.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { bvar, port, lam, app, termEq } from '../../../src/kernel/term/term'
import { shift, betaReduce } from '../../../src/kernel/term/reduce'

describe('shift', () => {
  it('shifts free indices at or above the cutoff', () => {
    // under one binder, index 0 is bound (below cutoff 1), index 1 is free
    const t = lam(app(bvar(0), bvar(1)))
    expect(termEq(shift(1, 0, t), lam(app(bvar(0), bvar(2))))).toBe(true)
  })

  it('leaves ports and constants untouched', () => {
    const t = app(port('y'), bvar(0))
    expect(termEq(shift(2, 0, t), app(port('y'), bvar(2)))).toBe(true)
  })

  it('throws when negative d produces a negative index', () => {
    expect(() => shift(-1, 0, bvar(0))).toThrow(/negative index/)
    expect(() => shift(-2, 0, bvar(1))).toThrow(/negative index/)
  })

  it('leaves indices below the cutoff unchanged', () => {
    // shift(1, 2, ...) must not touch bvar(0) or bvar(1)
    const t = app(bvar(0), app(bvar(1), bvar(2)))
    expect(termEq(shift(1, 2, t), app(bvar(0), app(bvar(1), bvar(3))))).toBe(true)
  })
})

describe('betaReduce', () => {
  it('substitutes the argument for the bound variable', () => {
    // (\x. x x) y  →  y y
    expect(termEq(betaReduce(app(bvar(0), bvar(0)), port('y')), app(port('y'), port('y')))).toBe(true)
  })

  it('avoids capture: argument indices shift under inner binders', () => {
    // (\x. \y. x) z  where z is bvar(0) in the surrounding context
    // body = \. bvar(1); arg = bvar(0)  →  \. bvar(1)  (arg shifted under the binder)
    const body = lam(bvar(1))
    const arg = bvar(0)
    expect(termEq(betaReduce(body, arg), lam(bvar(1)))).toBe(true)
  })

  it('correctly shifts arg with multiple free bvars under nested binders', () => {
    // (\x. \y. x) (app(bvar(0), bvar(1)))
    // body = lam(bvar(1)), arg = app(bvar(0), bvar(1))
    // result = lam(app(bvar(1), bvar(2)))  -- under \y, bvar(0)→bvar(1), bvar(1)→bvar(2)
    const result = betaReduce(lam(bvar(1)), app(bvar(0), bvar(1)))
    expect(termEq(result, lam(app(bvar(1), bvar(2))))).toBe(true)
  })

  it('decrements indices above the substituted variable', () => {
    // (\x. bvar(1)) a — body refers past the binder; after reduction it is bvar(0)
    expect(termEq(betaReduce(bvar(1), port('a')), bvar(0))).toBe(true)
  })

  it('drops the argument when the binder is unused (K behavior)', () => {
    expect(termEq(betaReduce(port('c'), app(port('y'), port('y'))), port('c'))).toBe(true)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/reduce.test.ts`
Expected: FAIL — cannot resolve `reduce`.

- [ ] **Step 3: Implement**

`src/kernel/term/reduce.ts`:

```ts
import type { Term } from './term'
import { bvar, lam, app } from './term'

/** Add d to every bvar index >= cutoff. d may be negative (caller guarantees no index goes negative). */
export function shift(d: number, cutoff: number, t: Term): Term {
  switch (t.kind) {
    case 'bvar': {
      if (t.index < cutoff) return t
      const next = t.index + d
      // Unreachable from betaReduce (substitution removes all index-0 occurrences
      // before the decrement); guards direct callers of shift(-d, ...).
      if (next < 0) {
        throw new Error(`shift produced negative index ${next}; caller violated its guarantee (d=${d}, cutoff=${cutoff}, index=${t.index})`)
      }
      return bvar(next)
    }
    case 'lam': return lam(shift(d, cutoff + 1, t.body))
    case 'app': return app(shift(d, cutoff, t.fn), shift(d, cutoff, t.arg))
    case 'port':
    case 'const':
      return t
  }
}

/** Substitute s for bvar j in t, shifting s under binders. */
function subst(j: number, s: Term, t: Term): Term {
  switch (t.kind) {
    case 'bvar': return t.index === j ? s : t
    case 'lam': return lam(subst(j + 1, shift(1, 0, s), t.body))
    case 'app': return app(subst(j, s, t.fn), subst(j, s, t.arg))
    case 'port':
    case 'const':
      return t
  }
}

/** The body of a redex (\. body) applied to arg: shift(-1) ∘ subst(0, shift(1) arg). Standard de Bruijn beta. */
export function betaReduce(body: Term, arg: Term): Term {
  return shift(-1, 0, subst(0, shift(1, 0, arg), body))
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/reduce.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/reduce.ts tests/kernel/term/reduce.test.ts
git commit -m "feat(kernel): de Bruijn shift, substitution, beta reduction"
```

---

### Task 6: Single-step normal-order reduction with redex paths

**Files:**
- Modify: `src/kernel/term/reduce.ts`
- Test: `tests/kernel/term/step.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/step.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { bvar, port, lam, app, termEq } from '../../../src/kernel/term/term'
import { stepNormalOrder, applyStepAt, hasFreeBVar } from '../../../src/kernel/term/reduce'
import { parseTerm } from '../../../src/kernel/term/parse'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('stepNormalOrder', () => {
  it('returns null for terms in beta-normal form', () => {
    expect(stepNormalOrder(p('\\x. x'))).toBeNull()
    expect(stepNormalOrder(p('f (g a)'))).toBeNull()
  })

  it('reduces the leftmost-outermost redex first', () => {
    // (\x. x) ((\y. y) a) — outer redex reduces first, path is []
    const t = p('(\\x. x) ((\\y. y) a)')
    const r = stepNormalOrder(t)
    expect(r).not.toBeNull()
    expect(r!.path).toEqual([])
    expect(termEq(r!.term, p('(\\y. y) a'))).toBe(true)
  })

  it('reduces under lambda when no outer redex exists', () => {
    const t = p('\\x. (\\y. y) x')
    const r = stepNormalOrder(t)
    expect(r).not.toBeNull()
    expect(r!.path).toEqual(['body'])
    expect(termEq(r!.term, p('\\x. x'))).toBe(true)
  })

  it('prefers fn-side redexes over arg-side', () => {
    const t = p('((\\x. x) f) ((\\y. y) a)')
    const r = stepNormalOrder(t)
    expect(r!.path).toEqual(['fn'])
    expect(termEq(r!.term, p('f ((\\y. y) a)'))).toBe(true)
  })

  it('steps omega to itself at the root', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const r = stepNormalOrder(omega)
    expect(r).not.toBeNull()
    expect(r!.path).toEqual([])
    expect(termEq(r!.term, omega)).toBe(true)
  })
})

describe('applyStepAt', () => {
  it('applies a beta step at an explicit path', () => {
    const t = p('((\\x. x) f) ((\\y. y) a)')
    const r = applyStepAt(t, { kind: 'beta', path: ['arg'] })
    expect(termEq(r, p('((\\x. x) f) a'))).toBe(true)
  })

  it('rejects a path that does not point at a redex of the claimed kind', () => {
    expect(() => applyStepAt(p('f a'), { kind: 'beta', path: [] }))
      .toThrowError(/no beta redex at path \[\]/i)
    expect(() => applyStepAt(p('\\x. x'), { kind: 'beta', path: ['fn'] }))
      .toThrowError(/invalid path segment 'fn'/i)
  })

  it('applies an eta step: \\x. f x → f when x not free in f', () => {
    const t = lam(app(port('f'), bvar(0)))
    expect(termEq(applyStepAt(t, { kind: 'eta', path: [] }), port('f'))).toBe(true)
  })

  it('applies an eta step under a non-empty path', () => {
    const t = lam(lam(app(port('f'), bvar(0))))
    expect(termEq(applyStepAt(t, { kind: 'eta', path: ['body'] }), lam(port('f')))).toBe(true)
  })

  it('rejects eta when the binder occurs in the function part', () => {
    // \x. x x is not an eta redex
    const t = lam(app(bvar(0), bvar(0)))
    expect(() => applyStepAt(t, { kind: 'eta', path: [] })).toThrowError(/no eta redex/i)
  })
})

describe('hasFreeBVar', () => {
  it('tracks indices through binders', () => {
    expect(hasFreeBVar(0, lam(bvar(1)))).toBe(true)
    expect(hasFreeBVar(0, lam(bvar(0)))).toBe(false)
    expect(hasFreeBVar(0, lam(lam(bvar(2))))).toBe(true)
    expect(hasFreeBVar(0, app(bvar(0), port('y')))).toBe(true)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/step.test.ts`
Expected: FAIL — `stepNormalOrder` / `applyStepAt` not exported.

- [ ] **Step 3: Implement (append to `src/kernel/term/reduce.ts`)**

```ts
export type PathSeg = 'body' | 'fn' | 'arg'
export type ReductionStep = { readonly kind: 'beta' | 'eta'; readonly path: readonly PathSeg[] }

/** True iff bvar with the given index occurs free in t. */
export function hasFreeBVar(index: number, t: Term): boolean {
  switch (t.kind) {
    case 'bvar': return t.index === index
    case 'lam': return hasFreeBVar(index + 1, t.body)
    case 'app': return hasFreeBVar(index, t.fn) || hasFreeBVar(index, t.arg)
    case 'port':
    case 'const':
      return false
  }
}

/**
 * One leftmost-outermost beta step. Returns the reduced term and the redex path,
 * or null if t is in beta-normal form. Normal order finds a normal form whenever
 * one exists, which is why it is the kernel's strategy.
 */
export function stepNormalOrder(t: Term): { term: Term; path: PathSeg[] } | null {
  if (t.kind === 'app' && t.fn.kind === 'lam') {
    return { term: betaReduce(t.fn.body, t.arg), path: [] }
  }
  switch (t.kind) {
    case 'lam': {
      const r = stepNormalOrder(t.body)
      return r === null ? null : { term: lam(r.term), path: ['body', ...r.path] }
    }
    case 'app': {
      const rf = stepNormalOrder(t.fn)
      if (rf !== null) return { term: app(rf.term, t.arg), path: ['fn', ...rf.path] }
      const ra = stepNormalOrder(t.arg)
      if (ra !== null) return { term: app(t.fn, ra.term), path: ['arg', ...ra.path] }
      return null
    }
    case 'bvar':
    case 'port':
    case 'const':
      return null
  }
}

/** Apply one named reduction step at an explicit path. Throws specifically when the path or redex is invalid. */
export function applyStepAt(t: Term, step: ReductionStep): Term {
  const fmt = (p: readonly PathSeg[]) => `[${p.join(', ')}]`
  if (step.path.length === 0) {
    if (step.kind === 'beta') {
      if (t.kind === 'app' && t.fn.kind === 'lam') return betaReduce(t.fn.body, t.arg)
      if (t.kind === 'app') {
        throw new Error(`no beta redex at path []: app fn is '${t.fn.kind}', not 'lam'`)
      }
      throw new Error(`no beta redex at path []: term head is '${t.kind}'`)
    }
    // eta: \x. f x with x not free in f  →  shift(-1, 0, f)
    if (t.kind === 'lam' && t.body.kind === 'app'
      && t.body.arg.kind === 'bvar' && t.body.arg.index === 0
      && !hasFreeBVar(0, t.body.fn)) {
      return shift(-1, 0, t.body.fn)
    }
    throw new Error(`no eta redex at path []: term is not of shape \\x. f x with x unused in f`)
  }
  const [seg, ...rest] = step.path
  const sub: ReductionStep = { kind: step.kind, path: rest }
  if (seg === 'body' && t.kind === 'lam') return lam(applyStepAt(t.body, sub))
  if (seg === 'fn' && t.kind === 'app') return app(applyStepAt(t.fn, sub), t.arg)
  if (seg === 'arg' && t.kind === 'app') return app(t.fn, applyStepAt(t.arg, sub))
  throw new Error(`invalid path segment '${seg}' into '${t.kind}' (remaining path ${fmt(step.path)})`)
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/step.test.ts`
Expected: PASS. Also re-run the full suite: `npm test` — all green.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/reduce.ts tests/kernel/term/step.test.ts
git commit -m "feat(kernel): normal-order stepping and path-addressed beta/eta steps"
```

---

### Task 7: Fueled normalization (β then η-fixpoint)

**Files:**
- Modify: `src/kernel/term/reduce.ts`
- Test: `tests/kernel/term/normalize.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/normalize.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { app, termEq, type Term } from '../../../src/kernel/term/term'
import { normalize, applyStepAt } from '../../../src/kernel/term/reduce'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

const ZERO = p('\\f. \\x. x')
const SUCC = p('\\n. \\f. \\x. f (n f x)')
const PLUS = p('\\m. \\n. \\f. \\x. m f (n f x)')
const TWO = p('\\f. \\x. f (f x)')
const OMEGA = p('(\\x. x x) (\\x. x x)')

const appChain = (...ts: Term[]) => ts.reduce((a, b) => app(a, b))

describe('normalize', () => {
  it('computes 1 + 1 = 2 on Church numerals', () => {
    const one = normalize(appChain(SUCC, ZERO), 1000)
    expect(one.status).toBe('normal')
    const sum = normalize(appChain(PLUS, one.term, one.term), 1000)
    expect(sum.status).toBe('normal')
    expect(termEq(sum.term, TWO), `expected Church 2, got ${printTerm(sum.term)}`).toBe(true)
  })

  it('eta-contracts after beta: \\f. \\x. f x reaches the eta-normal form \\x0. x0', () => {
    // inner body \x. f x eta-contracts to f, leaving \f. f — the identity
    const r = normalize(p('\\f. \\x. f x'), 100)
    expect(r.status).toBe('normal')
    expect(printTerm(r.term)).toBe('\\x0. x0')
  })

  it('records the full reduction path taken', () => {
    const r = normalize(p('(\\x. x) a'), 100)
    expect(r.status).toBe('normal')
    expect(r.path.length).toBe(1)
    expect(r.path[0]).toEqual({ kind: 'beta', path: [] })
  })

  it('reports fuel exhaustion loudly with the partial term and consumed path', () => {
    const r = normalize(OMEGA, 25)
    expect(r.status).toBe('fuel-exhausted')
    expect(r.path.length).toBe(25)
    // Omega reduces to itself forever
    expect(termEq(r.term, OMEGA)).toBe(true)
  })

  it('rejects non-positive fuel as a caller error', () => {
    expect(() => normalize(ZERO, 0)).toThrowError(/fuel must be a positive integer/i)
  })

  it('succeeds when fuel equals the exact step count (boundary)', () => {
    // (\x. x) a needs exactly 1 beta step
    const r1 = normalize(p('(\\x. x) a'), 1)
    expect(r1.status).toBe('normal')
    expect(r1.path.length).toBe(1)

    // \f. \x. f x needs exactly 1 eta step
    const r2 = normalize(p('\\f. \\x. f x'), 1)
    expect(r2.status).toBe('normal')
    expect(r2.path.length).toBe(1)
  })

  it('reports fuel-exhausted when fuel runs out during the eta phase', () => {
    // \a. \b. f a b needs 0 beta steps and exactly 2 eta steps
    const t = p('\\a. \\b. f a b')
    const exhausted = normalize(t, 1)
    expect(exhausted.status).toBe('fuel-exhausted')
    expect(exhausted.path.length).toBe(1)
    expect(exhausted.path[0]?.kind).toBe('eta')

    const ok = normalize(t, 2)
    expect(ok.status).toBe('normal')
    expect(ok.path.length).toBe(2)
  })

  it('recorded path is replayable via applyStepAt', () => {
    const t = p('(\\f. \\x. f x) (\\y. y)')
    const r = normalize(t, 100)
    expect(r.status).toBe('normal')
    let cur = t
    for (const step of r.path) {
      cur = applyStepAt(cur, step)
    }
    expect(termEq(cur, r.term)).toBe(true)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/normalize.test.ts`
Expected: FAIL — `normalize` not exported.

- [ ] **Step 3: Implement (append to `src/kernel/term/reduce.ts`)**

```ts
export type NormalizeResult =
  | { status: 'normal'; term: Term; path: readonly ReductionStep[] }
  | { status: 'fuel-exhausted'; term: Term; path: readonly ReductionStep[] }

/** One leftmost-outermost eta step, or null if eta-normal. */
export function stepEta(t: Term): { term: Term; path: PathSeg[] } | null {
  if (t.kind === 'lam' && t.body.kind === 'app'
    && t.body.arg.kind === 'bvar' && t.body.arg.index === 0
    && !hasFreeBVar(0, t.body.fn)) {
    return { term: shift(-1, 0, t.body.fn), path: [] }
  }
  switch (t.kind) {
    case 'lam': {
      const r = stepEta(t.body)
      return r === null ? null : { term: lam(r.term), path: ['body', ...r.path] }
    }
    case 'app': {
      const rf = stepEta(t.fn)
      if (rf !== null) return { term: app(rf.term, t.arg), path: ['fn', ...rf.path] }
      const ra = stepEta(t.arg)
      if (ra !== null) return { term: app(t.fn, ra.term), path: ['arg', ...ra.path] }
      return null
    }
    case 'bvar':
    case 'port':
    case 'const':
      return null
  }
}

/**
 * Fueled βη-normalization: normal-order beta to beta-normal form, then eta
 * contraction to fixpoint. Complete for finding βη-normal forms: normal order
 * finds the beta-normal form whenever one exists, and by eta-postponement the
 * eta steps can always be done after the beta steps. Each step consumes one
 * fuel unit; constants are opaque here (unfolding is the explicit rule 7).
 */
export function normalize(t: Term, fuel: number): NormalizeResult {
  if (!Number.isInteger(fuel) || fuel <= 0) {
    throw new Error(`fuel must be a positive integer, got ${fuel}`)
  }
  const path: ReductionStep[] = []
  let cur = t
  let remaining = fuel
  // Step is attempted before the fuel check so that normality always wins over
  // fuel: normalize(t, N) is 'normal' iff t reaches beta-eta-normal form in <= N steps.
  for (;;) {
    const b = stepNormalOrder(cur)
    if (b === null) break
    if (remaining === 0) return { status: 'fuel-exhausted', term: cur, path }
    path.push({ kind: 'beta', path: b.path })
    cur = b.term
    remaining--
  }
  for (;;) {
    const e = stepEta(cur)
    if (e === null) break
    if (remaining === 0) return { status: 'fuel-exhausted', term: cur, path }
    path.push({ kind: 'eta', path: e.path })
    cur = e.term
    remaining--
  }
  return { status: 'normal', term: cur, path }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/normalize.test.ts`
Expected: PASS. Re-run `npm test` — all green.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/reduce.ts tests/kernel/term/normalize.test.ts
git commit -m "feat(kernel): fueled beta-eta normalization with recorded paths"
```

---

### Task 8: Conversion certificates

**Files:**
- Create: `src/kernel/term/certificate.ts`
- Test: `tests/kernel/term/certificate.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/certificate.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { checkConversion, type ConversionCertificate } from '../../../src/kernel/term/certificate'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

const Y = p('\\f. (\\x. f (x x)) (\\x. f (x x))')
const YF = p('(\\f. (\\x. f (x x)) (\\x. f (x x))) g')         // Y g
const F_YF = p('g ((\\f. (\\x. f (x x)) (\\x. f (x x))) g)')   // g (Y g)

describe('checkConversion', () => {
  it('accepts Y g = g (Y g) via paths to a common reduct, despite no normal form existing', () => {
    // Y g →β (\x. g (x x)) (\x. g (x x)) →β g ((\x. g (x x)) (\x. g (x x)))
    // g (Y g) →β(inside arg) g ((\x. g (x x)) (\x. g (x x)))
    const cert: ConversionCertificate = {
      leftSteps: [
        { kind: 'beta', path: [] },
        { kind: 'beta', path: [] },
      ],
      rightSteps: [
        { kind: 'beta', path: ['arg'] },
      ],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok, result.ok ? '' : result.reason).toBe(true)
  })

  it('rejects a certificate whose paths do not meet', () => {
    const cert: ConversionCertificate = {
      leftSteps: [{ kind: 'beta', path: [] }],
      rightSteps: [],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok).toBe(false)
    if (!result.ok) {
      expect(result.reason).toMatch(/do not meet/i)
    }
  })

  it('rejects a certificate with an invalid step, naming the side and step index', () => {
    const cert: ConversionCertificate = {
      leftSteps: [{ kind: 'beta', path: ['fn', 'fn'] }],
      rightSteps: [],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok).toBe(false)
    if (!result.ok) {
      expect(result.reason).toMatch(/left step 0/i)
    }
  })

  it('rejects an invalid right step, naming the side and step index', () => {
    const cert: ConversionCertificate = {
      leftSteps: [],
      rightSteps: [{ kind: 'beta', path: ['fn', 'fn'] }],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok).toBe(false)
    if (!result.ok) {
      expect(result.reason).toMatch(/right step 0/i)
    }
  })

  it('accepts the trivial certificate for identical terms', () => {
    const result = checkConversion(Y, Y, { leftSteps: [], rightSteps: [] })
    expect(result.ok).toBe(true)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/certificate.test.ts`
Expected: FAIL — cannot resolve `certificate`.

- [ ] **Step 3: Implement**

`src/kernel/term/certificate.ts`:

```ts
import type { Term } from './term'
import { termEq } from './term'
import type { ReductionStep } from './reduce'
import { applyStepAt } from './reduce'

/**
 * A conversion certificate: explicit βη reduction paths from each side to a
 * common reduct (sound by Church–Rosser). This is the artifact stored in proof
 * steps so replay never re-searches: checking is mechanical and fuel-free.
 */
export type ConversionCertificate = {
  readonly leftSteps: readonly ReductionStep[]
  readonly rightSteps: readonly ReductionStep[]
}

export type ConversionCheck =
  | { ok: true; meet: Term }
  | { ok: false; reason: string }

export function checkConversion(left: Term, right: Term, cert: ConversionCertificate): ConversionCheck {
  let l = left
  for (const [i, step] of cert.leftSteps.entries()) {
    try {
      l = applyStepAt(l, step)
    } catch (e) {
      return { ok: false, reason: `left step ${i} is invalid: ${e instanceof Error ? e.message : String(e)}` }
    }
  }
  let r = right
  for (const [i, step] of cert.rightSteps.entries()) {
    try {
      r = applyStepAt(r, step)
    } catch (e) {
      return { ok: false, reason: `right step ${i} is invalid: ${e instanceof Error ? e.message : String(e)}` }
    }
  }
  if (!termEq(l, r)) {
    return { ok: false, reason: 'the two reduction paths do not meet at a common term' }
  }
  return { ok: true, meet: l }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/certificate.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/certificate.ts tests/kernel/term/certificate.test.ts
git commit -m "feat(kernel): conversion certificates checked by path replay"
```

---

### Task 9: Interactive convertibility (normalize-and-compare with certificate extraction)

**Files:**
- Create: `src/kernel/term/convert.ts`
- Test: `tests/kernel/term/convert.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/convert.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { convertible } from '../../../src/kernel/term/convert'
import { checkConversion } from '../../../src/kernel/term/certificate'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('convertible', () => {
  it('decides 1 + 1 = 2 and returns a checkable certificate', () => {
    const onePlusOne = p('(\\m. \\n. \\f. \\x. m f (n f x)) (\\f. \\x. f x) (\\f. \\x. f x)')
    const two = p('\\f. \\x. f (f x)')
    const r = convertible(onePlusOne, two, 1000)
    expect(r.status).toBe('convertible')
    if (r.status === 'convertible') {
      const check = checkConversion(onePlusOne, two, r.certificate)
      expect(check.ok, check.ok ? '' : check.reason).toBe(true)
    }
  })

  it('decides eta-equalities: \\x. f x = f, with a checkable certificate', () => {
    const left = p('\\x. f x')
    const right = p('f')
    const r = convertible(left, right, 100)
    expect(r.status).toBe('convertible')
    if (r.status === 'convertible') {
      const check = checkConversion(left, right, r.certificate)
      expect(check.ok, check.ok ? '' : check.reason).toBe(true)
    }
  })

  it('separates distinct normal forms definitively', () => {
    const r = convertible(p('\\f. \\x. f x'), p('\\f. \\x. f (f x)'), 100)
    expect(r.status).toBe('not-convertible')
  })

  it('reports fuel exhaustion distinctly — never a silent verdict', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const r = convertible(omega, p('\\x. x'), 25)
    expect(r.status).toBe('fuel-exhausted')
    if (r.status === 'fuel-exhausted') {
      expect(r.detail).toMatch(/left/i)
    }
  })

  it('names the right side when only the right side exhausts fuel', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const r = convertible(p('\\x. x'), omega, 25)
    expect(r.status).toBe('fuel-exhausted')
    if (r.status === 'fuel-exhausted') {
      expect(r.detail).toMatch(/right/i)
    }
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/convert.test.ts`
Expected: FAIL — cannot resolve `convert`.

- [ ] **Step 3: Implement**

`src/kernel/term/convert.ts`:

```ts
import type { Term } from './term'
import { termEq } from './term'
import { normalize } from './reduce'
import type { ConversionCertificate } from './certificate'

export type ConvertibleResult =
  | { status: 'convertible'; certificate: ConversionCertificate }
  | { status: 'not-convertible' }
  | { status: 'fuel-exhausted'; detail: string }

/**
 * Interactive equality: normalize both sides under the fuel budget and compare.
 * - Both normalize and meet: convertible, with the reduction paths as the certificate.
 * - Both normalize and differ: definitively not convertible (normal forms are unique).
 * - Either runs out of fuel: reported as such — the kernel never guesses.
 * Fuel affects this interactive search only; stored proofs carry certificates (§3.7 of the spec).
 * Constants are opaque at this layer; definitional unfolding is rule 7, a separate layer.
 * If left normalizes, right exhaustion is reported independently; when both sides would
 * exhaust, only the left is named — call normalize directly to diagnose both.
 */
export function convertible(left: Term, right: Term, fuel: number): ConvertibleResult {
  const l = normalize(left, fuel)
  if (l.status === 'fuel-exhausted') {
    return { status: 'fuel-exhausted', detail: `left term did not normalize within ${fuel} steps` }
  }
  const r = normalize(right, fuel)
  if (r.status === 'fuel-exhausted') {
    return { status: 'fuel-exhausted', detail: `right term did not normalize within ${fuel} steps` }
  }
  if (termEq(l.term, r.term)) {
    return { status: 'convertible', certificate: { leftSteps: l.path, rightSteps: r.path } }
  }
  return { status: 'not-convertible' }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/convert.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/convert.ts tests/kernel/term/convert.test.ts
git commit -m "feat(kernel): convertibility via normalize-and-compare with certificates"
```

---

### Task 10: Term serialization

**Files:**
- Create: `src/kernel/term/serialize.ts`
- Test: `tests/kernel/term/serialize.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/serialize.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { termEq } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { serializeTerm, deserializeTerm } from '../../../src/kernel/term/serialize'

const consts = new Set(['plus'])
const p = (s: string) => parseTerm(s, consts)

describe('serializeTerm', () => {
  it('round-trips every term shape', () => {
    for (const src of ['\\x. x', '\\f. \\x. f (f x)', 'plus m m', '\\x. y (y x)', 'f (\\x. x) b']) {
      const t = p(src)
      const back = deserializeTerm(serializeTerm(t))
      expect(termEq(t, back), `round-trip failed for ${src}`).toBe(true)
    }
  })

  it('is injective on distinct terms (serialization is the content key)', () => {
    const a = serializeTerm(p('\\x. x x'))
    const b = serializeTerm(p('\\x. x'))
    const c = serializeTerm(p('plus'))
    const d = serializeTerm(p('plus2 v'))
    expect(new Set([a, b, c, d]).size).toBe(4)
  })

  it('escapes names safely: a port named with quotes or parens cannot forge structure', () => {
    const tricky = { kind: 'port' as const, name: '"),A(' }
    const back = deserializeTerm(serializeTerm(tricky))
    expect(termEq(tricky, back)).toBe(true)
  })

  it('rejects malformed input loudly', () => {
    expect(() => deserializeTerm('L(')).toThrowError(/malformed/i)
    expect(() => deserializeTerm('garbage')).toThrowError(/malformed/i)
    expect(() => deserializeTerm('P("a")x')).toThrowError(/malformed/i)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/serialize.test.ts`
Expected: FAIL — cannot resolve `serialize`.

- [ ] **Step 3: Implement**

`src/kernel/term/serialize.ts`:

```ts
import type { Term } from './term'
import { bvar, port, cnst, lam, app } from './term'

/**
 * Stable, injective, ASCII serialization. De Bruijn makes this canonical for
 * alpha-equivalence by construction: equal serializations iff termEq. Names are
 * JSON-escaped so no name can forge structure. This string is the term-level
 * content key used by diagram canonicalization and fingerprints (Plan 2).
 */
export function serializeTerm(t: Term): string {
  switch (t.kind) {
    case 'bvar': return `#${t.index}`
    case 'port': return `P(${JSON.stringify(t.name)})`
    case 'const': return `C(${JSON.stringify(t.id)})`
    case 'lam': return `L(${serializeTerm(t.body)})`
    case 'app': return `A(${serializeTerm(t.fn)},${serializeTerm(t.arg)})`
  }
}

export function deserializeTerm(s: string): Term {
  const [term, rest] = parse(s, 0)
  if (rest !== s.length) throw new Error(`malformed term serialization: trailing input at ${rest}`)
  return term
}

function parse(s: string, i: number): [Term, number] {
  const fail = (msg: string): never => { throw new Error(`malformed term serialization at ${i}: ${msg}`) }
  const c = s[i] ?? fail('unexpected end')
  if (c === '#') {
    // Leading zeros are accepted; serializeTerm never emits them, so
    // non-canonical inputs decode to the unique canonical term.
    let j = i + 1
    while (j < s.length && s[j]! >= '0' && s[j]! <= '9') j++
    if (j === i + 1) fail('expected digits after #')
    return [bvar(Number(s.slice(i + 1, j))), j]
  }
  if (c === 'P' || c === 'C') {
    if (s[i + 1] !== '(') fail(`expected '(' after ${c}`)
    const [str, j] = parseJsonString(s, i + 2)
    if (s[j] !== ')') fail(`expected ')' closing ${c}(...)`)
    return [c === 'P' ? port(str) : cnst(str), j + 1]
  }
  if (c === 'L') {
    if (s[i + 1] !== '(') fail("expected '(' after L")
    const [body, j] = parse(s, i + 2)
    if (s[j] !== ')') fail("expected ')' closing L(...)")
    return [lam(body), j + 1]
  }
  if (c === 'A') {
    if (s[i + 1] !== '(') fail("expected '(' after A")
    const [fn, j] = parse(s, i + 2)
    if (s[j] !== ',') fail("expected ',' inside A(...)")
    const [arg, k] = parse(s, j + 1)
    if (s[k] !== ')') fail("expected ')' closing A(...)")
    return [app(fn, arg), k + 1]
  }
  return fail(`unexpected character '${c}'`)
}

function parseJsonString(s: string, i: number): [string, number] {
  if (s[i] !== '"') throw new Error(`malformed term serialization at ${i}: expected '"'`)
  let j = i + 1
  while (j < s.length) {
    if (s[j] === '\\') { j += 2; continue }
    if (s[j] === '"') {
      return [JSON.parse(s.slice(i, j + 1)) as string, j + 1]
    }
    j++
  }
  throw new Error(`malformed term serialization at ${i}: unterminated string`)
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `npx vitest run tests/kernel/term/serialize.test.ts`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/serialize.ts tests/kernel/term/serialize.test.ts
git commit -m "feat(kernel): injective ASCII term serialization with safe escaping"
```

---

### Task 11: Public module surface, full-suite gate, smoke-test removal

**Files:**
- Create: `src/kernel/term/index.ts`
- Delete: `tests/kernel/term/smoke.test.ts`

- [ ] **Step 1: Write the barrel module**

`src/kernel/term/index.ts`:

```ts
export type { Term } from './term'
export { bvar, port, cnst, lam, app, termEq, freePorts } from './term'
export { printTerm } from './print'
export { parseTerm, ParseError } from './parse'
export type { PathSeg, ReductionStep, NormalizeResult } from './reduce'
export { shift, betaReduce, hasFreeBVar, stepNormalOrder, stepEta, applyStepAt, normalize } from './reduce'
export type { ConversionCertificate, ConversionCheck } from './certificate'
export { checkConversion } from './certificate'
export type { ConvertibleResult } from './convert'
export { convertible } from './convert'
```

- [ ] **Step 2: Delete the scaffold smoke test**

```bash
rm tests/kernel/term/smoke.test.ts
```

(Its job — proving the harness runs — is done by every real test now. Dead tests are dead code.)

- [ ] **Step 3: Run the full suite and typecheck**

Run: `npm test && npm run typecheck`
Expected: all test files pass; typecheck exits 0.

- [ ] **Step 4: Commit**

```bash
git add src/kernel/term/index.ts
git rm tests/kernel/term/smoke.test.ts
git commit -m "feat(kernel): term-layer public surface; drop scaffold smoke test"
```

---

## Completion criteria for this plan

- `npm test` green, `npm run typecheck` clean.
- The term layer demonstrates, in its own tests: 1+1=2 by normalization; η-equalities; `Y g = g (Y g)` by certificate despite nonexistent normal forms; loud fuel exhaustion; loud rejection of every malformed input exercised.
- No DOM imports anywhere under `src/kernel/` (everything ran under Node).
- Plan 2 (diagram syntax, well-formedness, canonicalization) is written against these real exports.
