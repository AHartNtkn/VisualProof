# Random Theorem Generation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A "Random…" mode in the app that generates a random propositional tautology (two generator families: generate-and-shrink, kernel rule walk), labels its difficulty via a minimal-proof search over kernel moves, and commits it as the edit diagram for backward proving.

**Architecture:** Three isolated modules under `src/generate/` (pure propositional core + family A; kernel forward walk = family B; backward minimal-proof search) plus a UI panel `src/app/generate-entry.ts` modeled on `formula-entry.ts`. Nothing in the kernel changes.

**Tech Stack:** TypeScript (strict), vitest, Playwright. No new dependencies.

**Spec:** `docs/superpowers/specs/2026-08-14-random-theorem-generation-design.md` — read it before starting any task; it explains every decision this plan implements.

## Global Constraints

- No new npm dependencies.
- `npm run typecheck` must pass after every task.
- Ordinary vitest suite has a **5-second per-test timeout** (`vitest.suites.ts`); tests in `tests/generate/` are picked up automatically by the `tests/**/*.test.ts` glob. Keep search/generation tests within the timeout by choosing small knobs and fuel.
- Run a single test file with: `npx vitest run --config vitest.config.ts tests/generate/<file>.test.ts`
- Connectives are **{¬, ∧} only** in all generated formulas. ⊤/⊥ exist only inside the shrinker.
- All randomness flows through an injected `rng: () => number` returning values in [0,1). Tests use `seededRng` with fixed seeds. Never call `Math.random()` in `src/generate/`.
- Every failure is loud: throw with a message naming what failed and how to fix it. No silent skips, no `try {} catch {}` that swallows; catches must name the expected error class and rethrow everything else.
- Files stay well under the repo's 3000-line cap (`npm run formal:size`).
- Commit after each task with a specific message. Scope `git add` to the task's files only.
- Kernel import barrels: `src/kernel/diagram/index.ts` exports `polarity`, `cutDepth`, `isAncestorOrEqual`, `wireVisibleAt`, `sameDiagram`, `mkDiagramWithBoundary`, sig helpers; `src/kernel/proof/index.ts` exports `applyStep`, `checkTheorem`, `EMPTY_PROOF_CONTEXT`, `ProofStep`. Prefer barrels; fall back to the concrete module if a symbol is not re-exported (verify by reading the barrel, not by guessing).

---

### Task 1: Seeded RNG + propositional AST core

**Files:**
- Create: `src/generate/rng.ts`
- Create: `src/generate/prop/formula.ts`
- Test: `tests/generate/prop-formula.test.ts`

**Interfaces:**
- Produces: `seededRng(seed: number): () => number`; `PropFormula` union (`atom {index}` / `top` / `bot` / `not {body}` / `and {left, right}`); `evaluate(f, assignment: readonly boolean[]): boolean`; `isTautology(f, atoms: number): boolean`; `connectiveCount(f): number`; `usedAtoms(f): ReadonlySet<number>`; `atomName(index): string`; `printFormula(f): string`; `printTheorem(f): string`.

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/prop-formula.test.ts
import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import {
  atomName,
  connectiveCount,
  evaluate,
  isTautology,
  printFormula,
  printTheorem,
  usedAtoms,
  type PropFormula,
} from '../../src/generate/prop/formula'
import { parseFormula } from '../../src/formula/parse'
import type { Formula } from '../../src/formula/syntax'

const P: PropFormula = { kind: 'atom', index: 0 }
const Q: PropFormula = { kind: 'atom', index: 1 }
const not = (body: PropFormula): PropFormula => ({ kind: 'not', body })
const and = (left: PropFormula, right: PropFormula): PropFormula => ({ kind: 'and', left, right })
// ¬(P ∧ ¬P) — the law of noncontradiction, the running example of the spec.
const NONCONTRADICTION = not(and(P, not(P)))

/** Convert a parsed Formula body back to PropFormula, inverting atomName. */
function fromParsed(formula: Formula): PropFormula {
  switch (formula.kind) {
    case 'atom': {
      const index = [...Array(64).keys()].find((i) => atomName(i) === formula.name)
      if (index === undefined) throw new Error(`unexpected atom name '${formula.name}'`)
      return { kind: 'atom', index }
    }
    case 'not':
      return { kind: 'not', body: fromParsed(formula.body) }
    case 'and':
      return { kind: 'and', left: fromParsed(formula.left), right: fromParsed(formula.right) }
    default:
      throw new Error(`unexpected connective '${formula.kind}' in printed output`)
  }
}

describe('seededRng', () => {
  it('is deterministic for a fixed seed and stays within [0,1)', () => {
    const a = seededRng(42)
    const b = seededRng(42)
    const streamA = Array.from({ length: 100 }, () => a())
    const streamB = Array.from({ length: 100 }, () => b())
    expect(streamA).toEqual(streamB)
    for (const value of streamA) {
      expect(value).toBeGreaterThanOrEqual(0)
      expect(value).toBeLessThan(1)
    }
    expect(new Set(streamA).size).toBeGreaterThan(90)
  })
})

describe('evaluate / isTautology', () => {
  it('evaluates the truth table of ¬(P ∧ ¬P)', () => {
    expect(evaluate(NONCONTRADICTION, [true])).toBe(true)
    expect(evaluate(NONCONTRADICTION, [false])).toBe(true)
    expect(isTautology(NONCONTRADICTION, 1)).toBe(true)
  })
  it('rejects non-tautologies and evaluates constants', () => {
    expect(isTautology(P, 1)).toBe(false)
    expect(isTautology(and(P, not(P)), 1)).toBe(false)
    expect(evaluate({ kind: 'top' }, [])).toBe(true)
    expect(evaluate({ kind: 'bot' }, [])).toBe(false)
    // Peirce-ish two-atom tautology: ¬(¬(P∧Q) ∧ P ∧ Q) — spelled with binary ands.
    expect(isTautology(not(and(and(not(and(P, Q)), P), Q)), 2)).toBe(true)
  })
  it('throws loudly on an unassigned atom', () => {
    expect(() => evaluate(Q, [true])).toThrow(/atom 1/)
  })
})

describe('counting helpers', () => {
  it('counts connectives and used atoms', () => {
    expect(connectiveCount(NONCONTRADICTION)).toBe(3)
    expect(connectiveCount(P)).toBe(0)
    expect([...usedAtoms(and(P, and(Q, P)))].sort()).toEqual([0, 1])
  })
})

describe('printing', () => {
  it('names atoms as letters then numbered fallbacks', () => {
    expect(atomName(0)).toBe('P')
    expect(atomName(1)).toBe('Q')
    expect(atomName(7)).toBe('W')
    expect(atomName(8)).toBe('P8')
  })
  it('round-trips through parseFormula with correct precedence', () => {
    const cases: PropFormula[] = [
      NONCONTRADICTION,
      and(P, and(Q, P)),          // right-nested and needs parens
      and(and(P, Q), P),          // left-nested and needs none
      not(not(P)),
      and(not(P), not(and(P, Q))),
    ]
    for (const formula of cases) {
      const printed = printTheorem(formula)
      const parsed = parseFormula(printed)
      if (parsed.kind !== 'quantifier' || parsed.quantifier !== 'forall') {
        throw new Error(`printed theorem did not parse as a ∀: ${printed}`)
      }
      expect(fromParsed(parsed.body)).toEqual(formula)
    }
  })
  it('quantifies exactly the used atoms in index order', () => {
    expect(printTheorem(NONCONTRADICTION)).toBe('∀P:o. ¬(P ∧ ¬P)')
    expect(printTheorem(and(not(Q), Q)).startsWith('∀Q:o.')).toBe(true)
  })
  it('refuses to print constants or an atom-free formula', () => {
    expect(() => printFormula({ kind: 'top' })).toThrow(/constant/)
    expect(() => printTheorem(not({ kind: 'bot' }))).toThrow(/no atoms/)
  })
})
```

- [ ] **Step 2: Run the test, verify it fails** — `npx vitest run --config vitest.config.ts tests/generate/prop-formula.test.ts` — expect module-not-found failures.

- [ ] **Step 3: Implement**

```ts
// src/generate/rng.ts
/**
 * splitmix32 — a small deterministic PRNG (public-domain construction,
 * standard constants). Used so generated problems are reproducible from a
 * seed; not cryptographic. The UI seeds it from crypto.getRandomValues.
 */
export function seededRng(seed: number): () => number {
  let state = seed >>> 0
  return () => {
    state = (state + 0x9e3779b9) >>> 0
    let z = state
    z ^= z >>> 16
    z = Math.imul(z, 0x21f0aaad)
    z ^= z >>> 15
    z = Math.imul(z, 0x735a2d97)
    z ^= z >>> 15
    return (z >>> 0) / 4294967296
  }
}
```

```ts
// src/generate/prop/formula.ts
/**
 * Pure propositional core over {¬, ∧}. ⊤/⊥ exist only for the shrinker's
 * weakening substitutions and are never printed. Atom identity is a dense
 * index into the alphabet; printing maps indices to formula-language names.
 */
export type PropFormula =
  | { readonly kind: 'atom'; readonly index: number }
  | { readonly kind: 'top' }
  | { readonly kind: 'bot' }
  | { readonly kind: 'not'; readonly body: PropFormula }
  | { readonly kind: 'and'; readonly left: PropFormula; readonly right: PropFormula }

export function evaluate(formula: PropFormula, assignment: readonly boolean[]): boolean {
  switch (formula.kind) {
    case 'atom': {
      const value = assignment[formula.index]
      if (value === undefined) throw new Error(`evaluate: no assignment for atom ${formula.index}`)
      return value
    }
    case 'top':
      return true
    case 'bot':
      return false
    case 'not':
      return !evaluate(formula.body, assignment)
    case 'and':
      return evaluate(formula.left, assignment) && evaluate(formula.right, assignment)
  }
}

export function isTautology(formula: PropFormula, atoms: number): boolean {
  if (!Number.isInteger(atoms) || atoms < 0) throw new Error(`isTautology: bad alphabet size ${atoms}`)
  for (let bits = 0; bits < 2 ** atoms; bits += 1) {
    const assignment = Array.from({ length: atoms }, (_, index) => ((bits >> index) & 1) === 1)
    if (!evaluate(formula, assignment)) return false
  }
  return true
}

export function connectiveCount(formula: PropFormula): number {
  switch (formula.kind) {
    case 'atom':
    case 'top':
    case 'bot':
      return 0
    case 'not':
      return 1 + connectiveCount(formula.body)
    case 'and':
      return 1 + connectiveCount(formula.left) + connectiveCount(formula.right)
  }
}

export function usedAtoms(formula: PropFormula): ReadonlySet<number> {
  const atoms = new Set<number>()
  const visit = (node: PropFormula): void => {
    if (node.kind === 'atom') atoms.add(node.index)
    else if (node.kind === 'not') visit(node.body)
    else if (node.kind === 'and') {
      visit(node.left)
      visit(node.right)
    }
  }
  visit(formula)
  return atoms
}

const ATOM_LETTERS = ['P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W'] as const

export function atomName(index: number): string {
  return ATOM_LETTERS[index] ?? `P${index}`
}

/** Print with the parser's precedence: ¬ binds tighter than ∧; ∧ folds
 *  left-associatively, so only right-nested ∧ (and ∧ under ¬) needs parens. */
export function printFormula(formula: PropFormula): string {
  switch (formula.kind) {
    case 'atom':
      return atomName(formula.index)
    case 'top':
    case 'bot':
      throw new Error('printFormula: constants must be simplified away before printing')
    case 'not': {
      const body = printFormula(formula.body)
      return formula.body.kind === 'and' ? `¬(${body})` : `¬${body}`
    }
    case 'and': {
      const left = printFormula(formula.left)
      const right = printFormula(formula.right)
      return `${left} ∧ ${formula.right.kind === 'and' ? `(${right})` : right}`
    }
  }
}

/** Print the closed statement, ∀-quantifying exactly the used atoms. */
export function printTheorem(formula: PropFormula): string {
  const atoms = [...usedAtoms(formula)].sort((a, b) => a - b)
  if (atoms.length === 0) throw new Error('printTheorem: formula uses no atoms')
  return `∀${atoms.map(atomName).join(' ')}:o. ${printFormula(formula)}`
}
```

- [ ] **Step 4: Run the test, verify it passes.** Then `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/rng.ts src/generate/prop/formula.ts tests/generate/prop-formula.test.ts && git commit -m "add seeded rng and propositional formula core"`

---

### Task 2: Formula sampler

**Files:**
- Create: `src/generate/prop/sample.ts`
- Test: `tests/generate/prop-sample.test.ts`

**Interfaces:**
- Consumes: `PropFormula`, `connectiveCount`, `usedAtoms` from Task 1.
- Produces: `samplePropFormula(size: number, atoms: number, rng: () => number): PropFormula`.

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/prop-sample.test.ts
import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { connectiveCount, usedAtoms, type PropFormula } from '../../src/generate/prop/formula'
import { samplePropFormula } from '../../src/generate/prop/sample'

function assertShape(formula: PropFormula, atoms: number): void {
  switch (formula.kind) {
    case 'atom':
      expect(formula.index).toBeGreaterThanOrEqual(0)
      expect(formula.index).toBeLessThan(atoms)
      return
    case 'not':
      return assertShape(formula.body, atoms)
    case 'and':
      assertShape(formula.left, atoms)
      assertShape(formula.right, atoms)
      return
    default:
      throw new Error(`sampled formula contains forbidden node '${formula.kind}'`)
  }
}

describe('samplePropFormula', () => {
  it('produces exactly the requested connective count over {¬,∧} with in-range atoms', () => {
    const rng = seededRng(7)
    for (let round = 0; round < 200; round += 1) {
      const size = round % 15
      const formula = samplePropFormula(size, 3, rng)
      expect(connectiveCount(formula)).toBe(size)
      assertShape(formula, 3)
    }
  })
  it('is deterministic under a fixed seed', () => {
    expect(samplePropFormula(10, 2, seededRng(99))).toEqual(samplePropFormula(10, 2, seededRng(99)))
  })
  it('exercises the whole alphabet across draws', () => {
    const rng = seededRng(3)
    const seen = new Set<number>()
    for (let round = 0; round < 100; round += 1) {
      for (const atom of usedAtoms(samplePropFormula(6, 4, rng))) seen.add(atom)
    }
    expect([...seen].sort()).toEqual([0, 1, 2, 3])
  })
  it('rejects invalid parameters loudly', () => {
    expect(() => samplePropFormula(-1, 2, seededRng(1))).toThrow(/size/)
    expect(() => samplePropFormula(3, 0, seededRng(1))).toThrow(/atoms/)
  })
})
```

- [ ] **Step 2: Run it, verify failure** (module not found).
- [ ] **Step 3: Implement**

```ts
// src/generate/prop/sample.ts
import type { PropFormula } from './formula'

function rngIndex(rng: () => number, bound: number): number {
  const index = Math.floor(rng() * bound)
  if (!Number.isInteger(index) || index < 0 || index >= bound) {
    throw new Error(`rngIndex: rng produced out-of-range draw ${index} of ${bound}; rng must return [0,1)`)
  }
  return index
}

/**
 * Uniform random {¬,∧} formula with exactly `size` connectives: the root
 * connective is a fair coin between ¬ and ∧ (whenever size ≥ 1), and ∧
 * splits its remaining budget uniformly. Deliberately unbiased — quality
 * comes from the shrinker, not the sampler.
 */
export function samplePropFormula(size: number, atoms: number, rng: () => number): PropFormula {
  if (!Number.isInteger(size) || size < 0) throw new Error(`samplePropFormula: bad size ${size}`)
  if (!Number.isInteger(atoms) || atoms < 1) throw new Error(`samplePropFormula: bad atoms ${atoms}`)
  if (size === 0) return { kind: 'atom', index: rngIndex(rng, atoms) }
  if (rngIndex(rng, 2) === 0) {
    return { kind: 'not', body: samplePropFormula(size - 1, atoms, rng) }
  }
  const leftSize = rngIndex(rng, size) // 0 .. size-1; right gets the rest
  return {
    kind: 'and',
    left: samplePropFormula(leftSize, atoms, rng),
    right: samplePropFormula(size - 1 - leftSize, atoms, rng),
  }
}
```

- [ ] **Step 4: Run the test, verify it passes.** `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/prop/sample.ts tests/generate/prop-sample.test.ts && git commit -m "add uniform propositional formula sampler"`

---

### Task 3: Shrinker (minimality under weakening)

**Files:**
- Create: `src/generate/prop/shrink.ts`
- Test: `tests/generate/prop-shrink.test.ts`

**Interfaces:**
- Consumes: Task 1's `PropFormula`, `evaluate`, `isTautology`; Task 2's sampler (property test only).
- Produces: `simplify(f): PropFormula`; `weakenings(f): readonly PropFormula[]`; `shrinkToCore(f, atoms): PropFormula`; `isMinimalTautology(f, atoms): boolean`.

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/prop-shrink.test.ts
import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { isTautology, type PropFormula } from '../../src/generate/prop/formula'
import { samplePropFormula } from '../../src/generate/prop/sample'
import { isMinimalTautology, shrinkToCore, simplify, weakenings } from '../../src/generate/prop/shrink'

const P: PropFormula = { kind: 'atom', index: 0 }
const Q: PropFormula = { kind: 'atom', index: 1 }
const TOP: PropFormula = { kind: 'top' }
const BOT: PropFormula = { kind: 'bot' }
const not = (body: PropFormula): PropFormula => ({ kind: 'not', body })
const and = (left: PropFormula, right: PropFormula): PropFormula => ({ kind: 'and', left, right })
const NONCONTRADICTION = not(and(P, not(P)))

describe('simplify', () => {
  it('eliminates constants with the four identities', () => {
    expect(simplify(and(TOP, P))).toEqual(P)
    expect(simplify(and(P, BOT))).toEqual(BOT)
    expect(simplify(not(TOP))).toEqual(BOT)
    expect(simplify(not(not(BOT)))).toEqual(BOT)
    expect(simplify(and(not(BOT), and(TOP, Q)))).toEqual(Q)
  })
  it('leaves constant-free formulas untouched', () => {
    expect(simplify(NONCONTRADICTION)).toEqual(NONCONTRADICTION)
  })
})

describe('weakenings', () => {
  it('substitutes ⊥ at positive and ⊤ at negative occurrences', () => {
    // P ∧ ¬Q at positive root has exactly four occurrences:
    //   root (positive) → ⊥;  P (positive) → ⊥;
    //   ¬Q (positive) → ⊥;  Q (negative, under one ¬) → ⊤.
    const results = weakenings(and(P, not(Q)))
    expect(results).toHaveLength(4)
    expect(results).toContainEqual(BOT)
    expect(results).toContainEqual(and(BOT, not(Q)))
    expect(results).toContainEqual(and(P, BOT))
    expect(results).toContainEqual(and(P, not(TOP)))
  })
})

describe('shrinkToCore', () => {
  it('removes a junk conjunct-under-negation from the noncontradiction core', () => {
    // ¬(P ∧ ¬P ∧ Q): Q is dead weight (negative occurrence → ⊤ keeps validity).
    const junky = not(and(and(P, not(P)), Q))
    expect(isTautology(junky, 2)).toBe(true)
    expect(shrinkToCore(junky, 2)).toEqual(NONCONTRADICTION)
  })
  it('rejects non-tautology input loudly', () => {
    expect(() => shrinkToCore(P, 1)).toThrow(/not a tautology/)
  })
  it('property: every shrunk sampled tautology is minimal', () => {
    const rng = seededRng(2026)
    let tautologies = 0
    for (let round = 0; round < 400 && tautologies < 25; round += 1) {
      const sampled = samplePropFormula(10, 3, rng)
      if (!isTautology(sampled, 3)) continue
      tautologies += 1
      const core = shrinkToCore(sampled, 3)
      expect(isMinimalTautology(core, 3), `core of sample ${round} not minimal`).toBe(true)
    }
    expect(tautologies, 'sampler produced too few tautologies for the property test').toBeGreaterThan(10)
  })
})

describe('isMinimalTautology', () => {
  it('accepts the noncontradiction core and rejects padded variants', () => {
    expect(isMinimalTautology(NONCONTRADICTION, 1)).toBe(true)
    expect(isMinimalTautology(not(and(and(P, not(P)), Q)), 2)).toBe(false)
    expect(isMinimalTautology(P, 1)).toBe(false)          // not a tautology
    expect(isMinimalTautology(not(BOT), 0)).toBe(false)   // contains a constant
  })
})
```

- [ ] **Step 2: Run it, verify failure.**
- [ ] **Step 3: Implement**

```ts
// src/generate/prop/shrink.ts
import { isTautology, type PropFormula } from './formula'

const TOP: PropFormula = { kind: 'top' }
const BOT: PropFormula = { kind: 'bot' }

/** Constant elimination: ⊤∧φ≡φ, ⊥∧φ≡⊥, ¬⊤≡⊥, ¬⊥≡⊤, bottom-up. */
export function simplify(formula: PropFormula): PropFormula {
  switch (formula.kind) {
    case 'atom':
    case 'top':
    case 'bot':
      return formula
    case 'not': {
      const body = simplify(formula.body)
      if (body.kind === 'top') return BOT
      if (body.kind === 'bot') return TOP
      return body === formula.body ? formula : { kind: 'not', body }
    }
    case 'and': {
      const left = simplify(formula.left)
      const right = simplify(formula.right)
      if (left.kind === 'bot' || right.kind === 'bot') return BOT
      if (left.kind === 'top') return right
      if (right.kind === 'top') return left
      return left === formula.left && right === formula.right ? formula : { kind: 'and', left, right }
    }
  }
}

/**
 * All formulas obtained by replacing exactly one non-constant subformula
 * occurrence with its weakening constant (⊥ at positive polarity, ⊤ at
 * negative), in deterministic pre-order. With only {¬,∧} every occurrence
 * has a definite polarity.
 */
export function weakenings(formula: PropFormula): readonly PropFormula[] {
  const results: PropFormula[] = []
  const visit = (node: PropFormula, positive: boolean, rebuild: (r: PropFormula) => PropFormula): void => {
    if (node.kind === 'top' || node.kind === 'bot') return
    results.push(rebuild(positive ? BOT : TOP))
    if (node.kind === 'not') {
      visit(node.body, !positive, (r) => rebuild({ kind: 'not', body: r }))
    } else if (node.kind === 'and') {
      visit(node.left, positive, (r) => rebuild({ kind: 'and', left: r, right: node.right }))
      visit(node.right, positive, (r) => rebuild({ kind: 'and', left: node.left, right: r }))
    }
  }
  visit(formula, true, (replacement) => replacement)
  return results
}

/** Greedy fixpoint: keep applying the first validity-preserving weakening
 *  (then constant-simplifying) until none applies. The result is a minimal
 *  tautology — every remaining occurrence's weakening is falsifiable. */
export function shrinkToCore(formula: PropFormula, atoms: number): PropFormula {
  if (!isTautology(formula, atoms)) throw new Error('shrinkToCore: input is not a tautology')
  let current = simplify(formula)
  let shrunk = true
  while (shrunk) {
    shrunk = false
    for (const candidate of weakenings(current)) {
      if (isTautology(candidate, atoms)) {
        current = simplify(candidate)
        shrunk = true
        break
      }
    }
  }
  return current
}

function containsConstant(formula: PropFormula): boolean {
  switch (formula.kind) {
    case 'top':
    case 'bot':
      return true
    case 'atom':
      return false
    case 'not':
      return containsConstant(formula.body)
    case 'and':
      return containsConstant(formula.left) || containsConstant(formula.right)
  }
}

export function isMinimalTautology(formula: PropFormula, atoms: number): boolean {
  if (containsConstant(formula)) return false
  if (!isTautology(formula, atoms)) return false
  return weakenings(formula).every((candidate) => !isTautology(candidate, atoms))
}
```

- [ ] **Step 4: Run the test, verify it passes.** `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/prop/shrink.ts tests/generate/prop-shrink.test.ts && git commit -m "add weakening-based shrinker and minimality check"`

---

### Task 4: Family registry + family A (generate-and-shrink)

**Files:**
- Create: `src/generate/index.ts`
- Create: `src/generate/prop/family.ts`
- Test: `tests/generate/prop-family.test.ts`

**Interfaces:**
- Consumes: Tasks 1–3; `formulaToDiagram` from `src/formula`.
- Produces: `KnobSpec { id; label; min; default }`; `GeneratedProblem { diagram; statement; walkUpperBound? }`; `GeneratorFamily { id; label; description; knobs; generate(params, rng) }`; `readKnobs(family, params): Record<string, number>`; `propShrinkFamily`; `GENERATOR_FAMILIES` (ordered list, starts as `[propShrinkFamily]`).

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/prop-family.test.ts
import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES, readKnobs } from '../../src/generate'
import { propShrinkFamily } from '../../src/generate/prop/family'
import { connectiveCount, isTautology } from '../../src/generate/prop/formula'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { parseFormula } from '../../src/formula/parse'
import type { Formula } from '../../src/formula/syntax'
import type { PropFormula } from '../../src/generate/prop/formula'
import { atomName } from '../../src/generate/prop/formula'

function fromParsed(formula: Formula): PropFormula {
  switch (formula.kind) {
    case 'atom': {
      const index = [...Array(64).keys()].find((i) => atomName(i) === formula.name)
      if (index === undefined) throw new Error(`unexpected atom name '${formula.name}'`)
      return { kind: 'atom', index }
    }
    case 'not':
      return { kind: 'not', body: fromParsed(formula.body) }
    case 'and':
      return { kind: 'and', left: fromParsed(formula.left), right: fromParsed(formula.right) }
    default:
      throw new Error(`unexpected connective '${formula.kind}'`)
  }
}

describe('readKnobs', () => {
  it('applies defaults, enforces minima and integrality, rejects unknown keys', () => {
    expect(readKnobs(propShrinkFamily, {})).toEqual({ atoms: 3, sampleSize: 12, minSize: 6, attempts: 10_000 })
    expect(readKnobs(propShrinkFamily, { atoms: 2 }).atoms).toBe(2)
    expect(() => readKnobs(propShrinkFamily, { atoms: 0 })).toThrow(/atoms/)
    expect(() => readKnobs(propShrinkFamily, { atoms: 2.5 })).toThrow(/integer/)
    expect(() => readKnobs(propShrinkFamily, { bogus: 1 })).toThrow(/bogus/)
  })
})

describe('propShrinkFamily', () => {
  it('is registered first', () => {
    expect(GENERATOR_FAMILIES[0]?.id).toBe('prop-shrink')
  })
  it('generates minimal tautologies meeting the size knob, statement parseable and drawable', () => {
    const rng = seededRng(11)
    for (let round = 0; round < 3; round += 1) {
      const problem = propShrinkFamily.generate({ atoms: 2, sampleSize: 9, minSize: 3, attempts: 10_000 }, rng)
      const parsed = parseFormula(problem.statement)
      if (parsed.kind !== 'quantifier') throw new Error('statement is not quantified')
      const body = fromParsed(parsed.body)
      expect(isTautology(body, parsed.binders.length)).toBe(true)
      expect(isMinimalTautology(body, parsed.binders.length)).toBe(true)
      expect(connectiveCount(body)).toBeGreaterThanOrEqual(3)
      expect(problem.diagram.root).toBeDefined()
      expect(problem.walkUpperBound).toBeUndefined()
    }
  })
  it('throws loudly when the knobs are unsatisfiable within the attempt cap', () => {
    // A 1-connective core over 1 atom cannot reach 5 connectives minimum
    // when sampled at size 1 (cores never exceed the sampled size).
    expect(() => propShrinkFamily.generate({ atoms: 1, sampleSize: 1, minSize: 5, attempts: 50 }, seededRng(1)))
      .toThrow(/50 attempts/)
  })
})
```

- [ ] **Step 2: Run it, verify failure.**
- [ ] **Step 3: Implement**

```ts
// src/generate/index.ts
import type { Diagram } from '../kernel/diagram/diagram'
import { propShrinkFamily } from './prop/family'

export type KnobSpec = {
  readonly id: string
  readonly label: string
  /** Validity lower bound — values below are meaningless, not merely
   *  inadvisable. There are deliberately no maxima (spec decision). */
  readonly min: number
  readonly default: number
}

export type GeneratedProblem = {
  readonly diagram: Diagram
  readonly statement: string
  /** Family B only: recorded action count of the certifying derivation. */
  readonly walkUpperBound?: number
}

export type GeneratorFamily = {
  readonly id: string
  readonly label: string
  readonly description: string
  readonly knobs: readonly KnobSpec[]
  generate(params: Readonly<Record<string, number>>, rng: () => number): GeneratedProblem
}

/** Fill defaults, then validate every knob: integer and ≥ min. Unknown keys
 *  are an error — a typo must fail loudly, not silently fall to a default. */
export function readKnobs(
  family: GeneratorFamily,
  params: Readonly<Record<string, number>>,
): Record<string, number> {
  const known = new Set(family.knobs.map((knob) => knob.id))
  for (const key of Object.keys(params)) {
    if (!known.has(key)) throw new Error(`unknown knob '${key}' for family '${family.id}'`)
  }
  const values: Record<string, number> = {}
  for (const knob of family.knobs) {
    const value = params[knob.id] ?? knob.default
    if (!Number.isInteger(value)) throw new Error(`knob '${knob.id}' must be an integer, got ${value}`)
    if (value < knob.min) throw new Error(`knob '${knob.id}' must be ≥ ${knob.min}, got ${value}`)
    values[knob.id] = value
  }
  return values
}

export const GENERATOR_FAMILIES: readonly GeneratorFamily[] = [propShrinkFamily]
```

```ts
// src/generate/prop/family.ts
import { formulaToDiagram } from '../../formula'
import { readKnobs, type GeneratedProblem, type GeneratorFamily } from '../index'
import { connectiveCount, isTautology, printTheorem } from './formula'
import { samplePropFormula } from './sample'
import { shrinkToCore } from './shrink'

export const propShrinkFamily: GeneratorFamily = {
  id: 'prop-shrink',
  label: 'Random tautology (shrunk)',
  description: 'Samples random ¬/∧ formulas, keeps tautologies, and shrinks away every irrelevant part.',
  knobs: [
    { id: 'atoms', label: 'Atoms', min: 1, default: 3 },
    { id: 'sampleSize', label: 'Sample connectives', min: 1, default: 12 },
    { id: 'minSize', label: 'Minimum core connectives', min: 1, default: 6 },
    { id: 'attempts', label: 'Attempt cap', min: 1, default: 10_000 },
  ],
  generate(params, rng): GeneratedProblem {
    const knobs = readKnobs(propShrinkFamily, params)
    for (let attempt = 0; attempt < knobs.attempts!; attempt += 1) {
      const sampled = samplePropFormula(knobs.sampleSize!, knobs.atoms!, rng)
      if (!isTautology(sampled, knobs.atoms!)) continue
      const core = shrinkToCore(sampled, knobs.atoms!)
      if (connectiveCount(core) < knobs.minSize!) continue
      const statement = printTheorem(core)
      return { diagram: formulaToDiagram(statement), statement }
    }
    throw new Error(
      `prop-shrink: no core of ≥ ${knobs.minSize} connectives found in ${knobs.attempts} attempts; `
      + `lower 'Minimum core connectives' or raise 'Sample connectives' / 'Attempt cap'`,
    )
  },
}
```

Note the type-only cycle: `family.ts` imports `readKnobs` (a value) from `../index`, and `index.ts` imports `propShrinkFamily` from `./prop/family`. ESM handles this specific shape (both are function/const declarations used only at call time), but if the bundler or vitest complains about a cycle, move `KnobSpec`/`GeneratedProblem`/`GeneratorFamily`/`readKnobs` into a new `src/generate/registry.ts` with `index.ts` re-exporting them plus `GENERATOR_FAMILIES`; families then import from `../registry`. Do that restructuring rather than living with a fragile cycle warning.

- [ ] **Step 4: Run the test, verify it passes.** `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/index.ts src/generate/prop/family.ts tests/generate/prop-family.test.ts && git commit -m "add generator family registry and generate-and-shrink family"`

---

### Task 5: Diagram scan helpers + prop-fragment reader

**Files:**
- Create: `src/generate/diagram-scan.ts`
- Create: `src/generate/prop/read.ts`
- Test: `tests/generate/prop-read.test.ts`

**Interfaces:**
- Consumes: kernel `Diagram` types; `formulaToDiagram`; Task 1 printing.
- Produces: `childCuts(d, parent): readonly RegionId[]`; `nodesIn(d, region): readonly NodeId[]`; `propWires(d): readonly WireId[]`; `bareWires(d): readonly WireId[]`; `headWireOf(d, nodeId): WireId`; `readPropTheorem(d): { formula: PropFormula; wires: readonly WireId[] }`.

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/prop-read.test.ts
import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { sameDiagram } from '../../src/kernel/diagram'
import { printTheorem, usedAtoms } from '../../src/generate/prop/formula'
import { readPropTheorem } from '../../src/generate/prop/read'

const STATEMENTS = [
  '∀P:o. ¬(P ∧ ¬P)',
  '∀P Q:o. ¬(¬(P ∧ Q) ∧ P ∧ Q)',
  '∀P Q:o. ¬(P ∧ ¬P) ∧ ¬(Q ∧ ¬Q)',
  '∀P:o. ¬¬¬(P ∧ ¬P)',
]

describe('readPropTheorem', () => {
  it('round-trips statements through the formula pipeline up to isomorphism', () => {
    for (const statement of STATEMENTS) {
      const diagram = formulaToDiagram(statement)
      const reading = readPropTheorem(diagram)
      expect(usedAtoms(reading.formula).size).toBe(reading.wires.length)
      const reprinted = printTheorem(reading.formula)
      expect(sameDiagram(formulaToDiagram(reprinted), diagram)).toBe(true)
    }
  })
  it('rejects diagrams outside the propositional ∀-shell fragment', () => {
    // No shell at all: a bare noncontradiction over an unquantified shape.
    expect(() => readPropTheorem(formulaToDiagram('∀x:i. ∀Z:i→o. ¬(Z(x) ∧ ¬Z(x))')))
      .toThrow(/readPropTheorem/)
  })
})
```

- [ ] **Step 2: Run it, verify failure.**
- [ ] **Step 3: Implement**

```ts
// src/generate/diagram-scan.ts
import type { Diagram, NodeId, RegionId, WireId } from '../kernel/diagram/diagram'
import { relSig, sigEquals } from '../kernel/diagram/sig'

const PROPOSITION = relSig([])

export function childCuts(diagram: Diagram, parent: RegionId): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) => region.kind === 'cut' && region.parent === parent)
    .map(([id]) => id)
    .sort()
}

export function nodesIn(diagram: Diagram, region: RegionId): readonly NodeId[] {
  return Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)
    .sort()
}

/** Wires of the nullary-relation (proposition) signature. */
export function propWires(diagram: Diagram): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => sigEquals(wire.sig, PROPOSITION))
    .map(([id]) => id)
    .sort()
}

/** Wires all of whose endpoints are arity-1 identity pins (vacuity-deletable). */
export function bareWires(diagram: Diagram): readonly WireId[] {
  return Object.entries(diagram.wires)
    .filter(([, wire]) => wire.endpoints.every(({ node }) => {
      const at = diagram.nodes[node]
      return at !== undefined && at.kind === 'identity' && at.arity === 1
    }))
    .map(([id]) => id)
    .sort()
}

/** The wire attached to an atom node's head port. */
export function headWireOf(diagram: Diagram, nodeId: NodeId): WireId {
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wire.endpoints.some(({ node, port }) => node === nodeId && port.kind === 'head')) return wireId
  }
  throw new Error(`headWireOf: atom node '${nodeId}' has no head wire`)
}
```

```ts
// src/generate/prop/read.ts
import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import { relSig, sigEquals } from '../../kernel/diagram/sig'
import { childCuts, headWireOf, nodesIn, propWires } from '../diagram-scan'
import type { PropFormula } from './formula'

export type PropTheoremReading = {
  readonly formula: PropFormula
  readonly wires: readonly WireId[]
}

/**
 * Read a closed propositional ∀-shell diagram back into a PropFormula:
 * root sheet holds exactly the shell's outer cut; the annulus holds the
 * proposition wires' pins; the inner cut is the body; inside, cuts are ¬,
 * juxtaposition is ∧, and atom heads are proposition occurrences. Pins are
 * presentational and skipped everywhere; anything else is a loud error.
 * Atom indices are positions in the id-sorted proposition wire list.
 */
export function readPropTheorem(diagram: Diagram): PropTheoremReading {
  const fail = (message: string): never => {
    throw new Error(`readPropTheorem: ${message}`)
  }
  const wires = propWires(diagram)
  if (wires.length !== Object.keys(diagram.wires).length) fail('diagram has non-proposition wires')
  const rootCuts = childCuts(diagram, diagram.root)
  if (nodesIn(diagram, diagram.root).length !== 0 || rootCuts.length !== 1) {
    fail('expected exactly the ∀ shell at the root')
  }
  const outer = rootCuts[0]!
  const outerCuts = childCuts(diagram, outer)
  if (outerCuts.length !== 1) fail('expected a single body cut inside the shell')
  for (const nodeId of nodesIn(diagram, outer)) {
    const node = diagram.nodes[nodeId]!
    if (!(node.kind === 'identity' && node.arity === 1)) fail(`annulus holds a non-pin node '${nodeId}'`)
  }
  const wireIndex = new Map(wires.map((id, index) => [id, index]))
  const readRegion = (region: RegionId): PropFormula => {
    const items: PropFormula[] = []
    for (const nodeId of nodesIn(diagram, region)) {
      const node = diagram.nodes[nodeId]!
      if (node.kind === 'identity' && node.arity === 1) continue
      if (node.kind !== 'atom') fail(`body holds unsupported node '${nodeId}' (${node.kind})`)
      if (!sigEquals(node.sig, relSig([]))) fail(`atom '${nodeId}' is not propositional`)
      const index = wireIndex.get(headWireOf(diagram, nodeId))
      if (index === undefined) fail(`atom '${nodeId}' heads an unknown wire`)
      items.push({ kind: 'atom', index: index! })
    }
    for (const cut of childCuts(diagram, region)) {
      items.push({ kind: 'not', body: readRegion(cut) })
    }
    if (items.length === 0) return { kind: 'top' }
    return items.reduce((left, right) => ({ kind: 'and', left, right }))
  }
  return { formula: readRegion(outerCuts[0]!), wires }
}
```

- [ ] **Step 4: Run the test, verify it passes.** If `sameDiagram` fails on a round-trip, diff the two diagrams' region/node/wire tables by hand (they are small) — the likely causes are pin placement differences or ordering assumptions; fix the reader, never weaken the test to `toBe(false)`. `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/diagram-scan.ts src/generate/prop/read.ts tests/generate/prop-read.test.ts && git commit -m "add diagram scan helpers and propositional fragment reader"`

---

### Task 6: Atomic move enumerator

**Files:**
- Create: `src/generate/moves.ts`
- Test: `tests/generate/moves.test.ts`

**Interfaces:**
- Consumes: Task 5 scan helpers; kernel `polarity`, `isAncestorOrEqual`, `wireVisibleAt`, `applyStep`, `EMPTY_PROOF_CONTEXT`; `erasureStep`, `deiterationStep` from `src/app/interact/moves.ts`; `bareWireAssembly`, `bareWireDescription`, `RuleError` from `src/kernel/rules`.
- Produces: `MoveClass = 'erasure' | 'spawn' | 'doubleCut' | 'iteration' | 'vacuity'`; `CandidateMove { step: ProofStep; moveClass: MoveClass }`; `enumerateMoves(diagram, orientation, classes, within?): readonly CandidateMove[]`.

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/moves.test.ts
import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { applyStep, EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof'
import { enumerateMoves, type MoveClass } from '../../src/generate/moves'

const ALL: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration', 'vacuity'])
const NONCONTRADICTION = formulaToDiagram('∀P:o. ¬(P ∧ ¬P)')

describe('enumerateMoves', () => {
  it('soundness: every backward candidate applies (or is skipped as inapplicable by the applier)', () => {
    const candidates = enumerateMoves(NONCONTRADICTION, 'backward', ALL)
    expect(candidates.length).toBeGreaterThan(0)
    let applied = 0
    for (const candidate of candidates) {
      // The enumerator mirrors the gates; the applier is the authority. A
      // candidate the applier refuses is a bug in the enumerator's gate
      // mirroring, so every candidate must apply cleanly here.
      const next = applyStep(NONCONTRADICTION, candidate.step, EMPTY_PROOF_CONTEXT, 'backward')
      expect(Object.keys(next.regions).length).toBeGreaterThan(0)
      applied += 1
    }
    expect(applied).toBe(candidates.length)
  })
  it('offers the known moves on the noncontradiction diagram (backward)', () => {
    const candidates = enumerateMoves(NONCONTRADICTION, 'backward', ALL)
    const rules = new Set(candidates.map(({ step }) => step.rule))
    expect(rules.has('deiteration')).toBe(true)   // inner P justified by outer P
    expect(rules.has('erasure')).toBe(true)       // e.g. P in the negative body cut
    expect(rules.has('doubleCutIntro')).toBe(true)
    expect(rules.has('atomSpawn')).toBe(true)     // positive regions exist
    expect(rules.has('doubleCutElim')).toBe(false) // no empty annulus yet
  })
  it('respects the within-region frame: no moves touch the shell from inside a frame', () => {
    // Frame the enumeration at the body cut: no candidate's step may target
    // the root or the shell cuts, and doubleCutElim never targets the frame.
    const diagram = NONCONTRADICTION
    const shellRegions = new Set([diagram.root])
    const candidates = enumerateMoves(diagram, 'backward', ALL, bodyRegion(diagram))
    for (const { step } of candidates) {
      if ('region' in step) expect(shellRegions.has(step.region)).toBe(false)
      if ('sel' in step) expect(shellRegions.has(step.sel.region)).toBe(false)
    }
  })
  it('forward orientation flips the deletion/insertion gates', () => {
    const backward = enumerateMoves(NONCONTRADICTION, 'backward', new Set(['erasure', 'spawn']))
    const forward = enumerateMoves(NONCONTRADICTION, 'forward', new Set(['erasure', 'spawn']))
    const regionsOf = (moves: typeof forward, rule: string): Set<string> =>
      new Set(moves.filter(({ step }) => step.rule === rule)
        .map(({ step }) => ('region' in step ? step.region : 'sel' in step ? step.sel.region : '')))
    // A region offering backward erasure (negative) must not offer forward erasure.
    for (const region of regionsOf(backward, 'erasure')) {
      expect(regionsOf(forward, 'erasure').has(region)).toBe(false)
    }
    for (const region of regionsOf(backward, 'atomSpawn')) {
      expect(regionsOf(forward, 'atomSpawn').has(region)).toBe(false)
    }
  })
})

function bodyRegion(diagram: ReturnType<typeof formulaToDiagram>): string {
  const cutsUnder = (parent: string): string[] =>
    Object.entries(diagram.regions)
      .filter(([, region]) => region.kind === 'cut' && region.parent === parent)
      .map(([id]) => id)
  const outer = cutsUnder(diagram.root)[0]!
  return cutsUnder(outer)[0]!
}
```

- [ ] **Step 2: Run it, verify failure.**
- [ ] **Step 3: Implement**

```ts
// src/generate/moves.ts
import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import { isAncestorOrEqual, polarity, wireVisibleAt } from '../kernel/diagram'
import { relSig } from '../kernel/diagram/sig'
import type { ProofStep } from '../kernel/proof'
import type { SubgraphSelection } from '../kernel/diagram'
import { bareWireAssembly, bareWireDescription, RuleError } from '../kernel/rules'
import { deiterationStep, erasureStep } from '../app/interact/moves'
import { bareWires, childCuts, nodesIn, propWires } from './diagram-scan'

export type MoveClass = 'erasure' | 'spawn' | 'doubleCut' | 'iteration' | 'vacuity'

export type CandidateMove = {
  readonly step: ProofStep
  readonly moveClass: MoveClass
}

/**
 * Enumerate the atomic propositional move alphabet on `diagram`, restricted
 * to content inside `within` (the frame region itself is never removed).
 * Atomic selections are a single atom node or a single cut with its whole
 * subtree. Gates are mirrored from the appliers; the applier remains the
 * authority — callers apply each candidate and treat a `RuleError` as the
 * candidate being withdrawn.
 */
export function enumerateMoves(
  diagram: Diagram,
  orientation: 'forward' | 'backward',
  classes: ReadonlySet<MoveClass>,
  within: RegionId = diagram.root,
): readonly CandidateMove[] {
  const out: CandidateMove[] = []
  const regions = Object.keys(diagram.regions)
    .filter((region) => isAncestorOrEqual(diagram, within, region))
    .sort()
  const atomicSelections: SubgraphSelection[] = []
  for (const region of regions) {
    for (const nodeId of nodesIn(diagram, region)) {
      if (diagram.nodes[nodeId]!.kind === 'atom') {
        atomicSelections.push({ region, regions: [], nodes: [nodeId], wires: [] })
      }
    }
    for (const cut of childCuts(diagram, region)) {
      atomicSelections.push({ region, regions: [cut], nodes: [], wires: [] })
    }
  }
  const deletionPolarity = orientation === 'forward' ? 'positive' : 'negative'
  const insertionPolarity = orientation === 'forward' ? 'negative' : 'positive'

  if (classes.has('erasure')) {
    for (const sel of atomicSelections) {
      if (polarity(diagram, sel.region) !== deletionPolarity) continue
      out.push({ moveClass: 'erasure', step: erasureStep(diagram, sel) })
    }
  }
  if (classes.has('spawn')) {
    for (const region of regions) {
      if (polarity(diagram, region) !== insertionPolarity) continue
      for (const wire of propWires(diagram)) {
        if (!wireVisibleAt(diagram, wire, region)) continue
        out.push({ moveClass: 'spawn', step: { rule: 'atomSpawn', region, wire } })
      }
    }
  }
  if (classes.has('doubleCut')) {
    for (const region of regions) {
      out.push({
        moveClass: 'doubleCut',
        step: { rule: 'doubleCutIntro', sel: { region, regions: [], nodes: [], wires: [] } },
      })
    }
    for (const sel of atomicSelections) {
      out.push({ moveClass: 'doubleCut', step: { rule: 'doubleCutIntro', sel } })
    }
    for (const region of regions) {
      // doubleCutElim removes `region` itself, so the frame is excluded; the
      // annulus must hold exactly one child cut and no nodes.
      if (region === within) continue
      if (diagram.regions[region]!.kind !== 'cut') continue
      if (childCuts(diagram, region).length !== 1) continue
      if (nodesIn(diagram, region).length !== 0) continue
      out.push({ moveClass: 'doubleCut', step: { rule: 'doubleCutElim', region } })
    }
  }
  if (classes.has('iteration')) {
    for (const sel of atomicSelections) {
      const copiedCut = sel.regions[0]
      for (const target of regions) {
        if (!isAncestorOrEqual(diagram, sel.region, target)) continue
        if (copiedCut !== undefined && isAncestorOrEqual(diagram, copiedCut, target)) continue
        out.push({ moveClass: 'iteration', step: { rule: 'iteration', sel, target } })
      }
      try {
        out.push({ moveClass: 'iteration', step: deiterationStep(diagram, sel) })
      } catch (error) {
        // No exact justifying occurrence — deiteration of this selection is
        // simply not offered. Anything else is a real bug: rethrow.
        if (!(error instanceof RuleError)) throw error
      }
    }
  }
  if (classes.has('vacuity')) {
    for (const wireId of bareWires(diagram)) {
      out.push({ moveClass: 'vacuity', step: { rule: 'vacuity', direction: 'delete', assembly: bareWireDescription(diagram, wireId) } })
    }
    for (const region of regions) {
      out.push({ moveClass: 'vacuity', step: { rule: 'vacuity', direction: 'insert', assembly: bareWireAssembly(freshWireLabel(diagram), region, relSig([])) } })
    }
  }
  return out
}

function freshWireLabel(diagram: Diagram): WireId {
  let counter = 0
  while (diagram.wires[`genw${counter}`] !== undefined || diagram.nodes[`genw${counter}_end0`] !== undefined) {
    counter += 1
  }
  return `genw${counter}`
}
```

Import-path caveat: verify each symbol against the barrels before assuming (`SubgraphSelection` is exported from `src/kernel/diagram/index.ts`; `RuleError`, `bareWireAssembly`, `bareWireDescription` from `src/kernel/rules/index.ts` — read those barrels and adjust imports to what actually exists). The `src/generate` → `src/app/interact/moves.ts` import is acyclic at file level (that module does not import `src/generate`).

- [ ] **Step 4: Run the test, verify it passes.** If a soundness case fails, the enumerator's gate mirroring is wrong — fix the enumerator (e.g. a missed scope-preservation case in erasure candidates); as a last resort for erasure candidates whose apply raises `ScopePreservationError`-style refusals, drop that candidate in the enumerator by pre-applying `applyStep` in a `try`/`catch (RuleError)` — but only after understanding why the mirror missed it, and record the reason in a comment. `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/moves.ts tests/generate/moves.test.ts && git commit -m "add atomic propositional move enumerator"`

---

### Task 7: Family B — kernel forward walk

**Files:**
- Create: `src/generate/walk/family.ts`
- Modify: `src/generate/index.ts` (append `propWalkFamily` to `GENERATOR_FAMILIES`)
- Test: `tests/generate/walk-family.test.ts`

**Interfaces:**
- Consumes: `PrimitiveStepRecorder`, `onlyNewCut` from `src/theories/record`; `emptyGraph`, `finishDiagramWithBoundary` from `src/theories/graph`; `EMPTY_PROOF_CONTEXT`, `checkTheorem` from `src/kernel/proof`; `mkDiagramWithBoundary` from `src/kernel/diagram`; `bareWireAssembly`, `RuleError` from `src/kernel/rules`; `relSig`; Tasks 1, 3, 5, 6.
- Produces: `propWalkFamily: GeneratorFamily` (id `prop-walk`).

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/walk-family.test.ts
import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES } from '../../src/generate'
import { propWalkFamily } from '../../src/generate/walk/family'
import { readPropTheorem } from '../../src/generate/prop/read'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { usedAtoms } from '../../src/generate/prop/formula'
import { formulaToDiagram } from '../../src/formula'
import { sameDiagram } from '../../src/kernel/diagram'

describe('propWalkFamily', () => {
  it('is registered second', () => {
    expect(GENERATOR_FAMILIES.map(({ id }) => id)).toEqual(['prop-shrink', 'prop-walk'])
  })
  it('generates certified, minimal, readable theorems (seed batch)', () => {
    for (const seed of [1, 2, 3]) {
      const problem = propWalkFamily.generate(
        { atoms: 2, length: 6, attempts: 200 },
        seededRng(seed),
      )
      // checkTheorem already ran inside generate (it throws on a bad
      // derivation); re-verify the outward contract here:
      const reading = readPropTheorem(problem.diagram)
      expect(usedAtoms(reading.formula).size).toBe(reading.wires.length)
      expect(isMinimalTautology(reading.formula, reading.wires.length)).toBe(true)
      expect(sameDiagram(formulaToDiagram(problem.statement), problem.diagram)).toBe(true)
      expect(problem.walkUpperBound).toBeGreaterThan(0)
    }
  })
  it('throws loudly when the attempt cap is exhausted', () => {
    // attempts=1 with a long walk over 1 atom essentially never survives the
    // minimality filter on the first try for this seed; assert the loud error.
    expect(() => propWalkFamily.generate({ atoms: 1, length: 12, attempts: 1 }, seededRng(4)))
      .toThrow(/attempts/)
  })
})
```

If the third test's specific seed happens to survive the filter, pick the next seed that does not (verify by observation, note the seed choice in a comment) — the test's subject is the loud cap error, not the survival odds.

- [ ] **Step 2: Run it, verify failure.**
- [ ] **Step 3: Implement**

```ts
// src/generate/walk/family.ts
import { EMPTY_PROOF_CONTEXT, checkTheorem } from '../../kernel/proof'
import { mkDiagramWithBoundary } from '../../kernel/diagram'
import { relSig } from '../../kernel/diagram/sig'
import { bareWireAssembly, RuleError } from '../../kernel/rules'
import { emptyGraph, finishDiagramWithBoundary } from '../../theories/graph'
import { PrimitiveStepRecorder, onlyNewCut } from '../../theories/record'
import { readKnobs, type GeneratedProblem, type GeneratorFamily } from '../index'
import { atomName, printTheorem, usedAtoms } from '../prop/formula'
import { isMinimalTautology } from '../prop/shrink'
import { readPropTheorem } from '../prop/read'
import { enumerateMoves, type CandidateMove, type MoveClass } from '../moves'

/**
 * Walk move weights. Distribution shaping ONLY — legality always comes from
 * enumerating actually-applicable moves, and no correctness property depends
 * on these values. The ordering encodes the spec's bias: iteration/deiteration
 * and double-cut moves build reusable structure; atomSpawn is the junk source
 * (it is insertion, seen from the player's backward proof); erasure undoes
 * walk progress. The minimality filter, not the weights, guarantees quality.
 */
const WALK_CLASS_WEIGHTS: Readonly<Record<MoveClass, number>> = {
  iteration: 4,
  doubleCut: 3,
  spawn: 2,
  erasure: 1,
  vacuity: 0, // excluded from the walk alphabet below; listed for the type
}
const WALK_CLASSES: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration'])

export const propWalkFamily: GeneratorFamily = {
  id: 'prop-walk',
  label: 'Random tautology (rule walk)',
  description: 'Applies real kernel rules forward from the blank sheet; every problem carries a checked derivation.',
  knobs: [
    { id: 'atoms', label: 'Atoms', min: 1, default: 2 },
    { id: 'length', label: 'Walk length', min: 1, default: 12 },
    { id: 'attempts', label: 'Attempt cap', min: 1, default: 1_000 },
  ],
  generate(params, rng): GeneratedProblem {
    const knobs = readKnobs(propWalkFamily, params)
    for (let attempt = 0; attempt < knobs.attempts!; attempt += 1) {
      const problem = tryWalk(knobs.atoms!, knobs.length!, rng)
      if (problem !== null) return problem
    }
    throw new Error(
      `prop-walk: no walk survived the minimality filter in ${knobs.attempts} attempts; `
      + `try a longer walk or raise 'Attempt cap'`,
    )
  },
}

function tryWalk(atoms: number, length: number, rng: () => number): GeneratedProblem | null {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const recorder = new PrimitiveStepRecorder(lhs, EMPTY_PROOF_CONTEXT, 'forward')
  // Prelude: the ∀ shell — an empty double cut, then one bare proposition
  // wire per atom vacuity-inserted into the annulus (matching the shape
  // quantifierScope('forall') produces).
  let before = recorder.diagram
  recorder.record('open universal shell', {
    rule: 'doubleCutIntro',
    sel: { region: recorder.diagram.root, regions: [], nodes: [], wires: [] },
  })
  const outer = onlyNewCut(before, recorder.diagram, recorder.diagram.root)
  const inner = onlyNewCut(before, recorder.diagram, outer)
  for (let index = 0; index < atoms; index += 1) {
    recorder.record(`declare proposition ${atomName(index)}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly(`genp${index}`, outer, relSig([])),
    })
  }
  for (let move = 0; move < length; move += 1) {
    const candidates = enumerateMoves(recorder.diagram, 'forward', WALK_CLASSES, inner)
    if (!applyWeightedRandomMove(recorder, candidates, rng)) return null
  }
  const diagram = recorder.diagram
  // Certification: replay the recorded derivation from the blank sheet.
  checkTheorem(
    { name: 'generated', lhs, rhs: mkDiagramWithBoundary(diagram, []), actions: recorder.actions },
    EMPTY_PROOF_CONTEXT,
  )
  // Polish filters (spec): readable, all wires used, minimal.
  let reading
  try {
    reading = readPropTheorem(diagram)
  } catch {
    // The walk left the propositional ∀-shell shape (e.g. it emptied the
    // body into a non-shell form). Not an error — this walk is rejected.
    return null
  }
  if (usedAtoms(reading.formula).size !== reading.wires.length) return null
  if (!isMinimalTautology(reading.formula, reading.wires.length)) return null
  return { diagram, statement: printTheorem(reading.formula), walkUpperBound: recorder.actions.length }
}

/** Weighted draw without replacement until one candidate applies. The
 *  recorder auto-pins on scope-preservation refusals; any other RuleError
 *  withdraws the candidate; non-RuleErrors are real bugs and propagate. */
function applyWeightedRandomMove(
  recorder: PrimitiveStepRecorder,
  candidates: readonly CandidateMove[],
  rng: () => number,
): boolean {
  const pool = [...candidates]
  while (pool.length > 0) {
    const total = pool.reduce((sum, candidate) => sum + WALK_CLASS_WEIGHTS[candidate.moveClass], 0)
    if (total <= 0) return false
    let draw = rng() * total
    let index = 0
    for (; index < pool.length - 1; index += 1) {
      draw -= WALK_CLASS_WEIGHTS[pool[index]!.moveClass]
      if (draw < 0) break
    }
    const candidate = pool.splice(index, 1)[0]!
    try {
      recorder.record(`walk ${candidate.step.rule}`, candidate.step)
      return true
    } catch (error) {
      if (!(error instanceof RuleError)) throw error
    }
  }
  return false
}
```

One bare `catch` above (around `readPropTheorem`) intentionally treats *any* reader rejection as walk rejection — the reader throws only its own descriptive errors. If you find that too broad while implementing, narrow it to `Error` messages prefixed `readPropTheorem:` and rethrow the rest.

- [ ] **Step 4: Run the test, verify it passes.** The `sameDiagram` cross-check is the hard assertion: if it fails, dump both diagrams (they are small JSON records) and compare pin placement between the walk's post-tidy shape and `formulaToDiagram`'s `finishDiagram` shape; fix the prelude (or reader) until they agree — do not delete the assertion. `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/walk/family.ts src/generate/index.ts tests/generate/walk-family.test.ts && git commit -m "add kernel rule-walk generator family"`

---

### Task 8: Minimal-proof search

**Files:**
- Create: `src/generate/search/digest.ts`
- Create: `src/generate/search/search.ts`
- Test: `tests/generate/search.test.ts`

**Interfaces:**
- Consumes: Task 6 enumerator; kernel `applyStep`, `EMPTY_PROOF_CONTEXT`, `sameDiagram`, `cutDepth`, `sigKey`; `RuleError` from `src/kernel/rules`; `ProofError` from `src/kernel/proof`.
- Produces: `diagramDigest(d): string`; `SearchOutcome = { status: 'solved'; mode: 'deletion-only' | 'full'; length; requires: readonly MoveClass[]; steps: readonly ProofStep[] } | { status: 'exhausted'; requiresInsertion: true; noProofWithin: number }`; `minimalProofSearch(start: Diagram, fuel: number): SearchOutcome`; `DEFAULT_SEARCH_FUEL` (named constant, `20_000` — the phase-2 budget, sized by the tests below and adjustable there, never silently).

**Two-phase design (spec, search section):** phase 1 searches the deletion-only alphabet (`erasure`, `deiteration`, `doubleCutElim`, vacuity-delete) — every such move strictly shrinks the diagram, so a BFS with isomorphism dedup explores the whole space with no fuel; a solve is an exact minimal deletion-only length, and full exhaustion *proves* the problem requires insertion. Phase 2 (only after that proof) is the fuel-bounded full-alphabet IDDFS.

- [ ] **Step 1: Write the failing test**

```ts
// tests/generate/search.test.ts
import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { seededRng } from '../../src/generate/rng'
import { propWalkFamily } from '../../src/generate/walk/family'
import { propShrinkFamily } from '../../src/generate/prop/family'
import { diagramDigest } from '../../src/generate/search/digest'
import { DEFAULT_SEARCH_FUEL, minimalProofSearch } from '../../src/generate/search/search'

describe('diagramDigest', () => {
  it('is invariant under id renaming but separates different shapes', () => {
    const a = formulaToDiagram('∀P:o. ¬(P ∧ ¬P)')
    const b = formulaToDiagram('∀Q:o. ¬(Q ∧ ¬Q)') // isomorphic, different ids
    const c = formulaToDiagram('∀P:o. ¬¬¬(P ∧ ¬P)')
    expect(diagramDigest(a)).toBe(diagramDigest(b))
    expect(diagramDigest(a)).not.toBe(diagramDigest(c))
  })
})

describe('minimalProofSearch', () => {
  it('solves ∀P:o. ¬(P∧¬P) deletion-only in exactly 5 moves, requiring the iteration class', () => {
    // Hand-computed minimal backward proof (see spec, Testing section):
    //   deiterate inner P → erase outer P (negative) → doubleCutElim body
    //   pair → vacuity-delete the bare wire → doubleCutElim the shell.
    // All five are deletion moves, so phase 1 solves it; the inner
    // (positive) cut can only be emptied by deiteration, so the iteration
    // class is required; insertion is proven unnecessary.
    const outcome = minimalProofSearch(formulaToDiagram('∀P:o. ¬(P ∧ ¬P)'), DEFAULT_SEARCH_FUEL)
    if (outcome.status !== 'solved') throw new Error(`expected a solve, got ${JSON.stringify(outcome)}`)
    expect(outcome.mode).toBe('deletion-only')
    expect(outcome.length).toBe(5)
    expect(outcome.steps).toHaveLength(5)
    expect(outcome.requires).toContain('iteration')
    expect(outcome.requires).not.toContain('spawn')
  })
  it('proves Peirce\'s law requires insertion, then reports an honest phase-2 result', () => {
    // ((P→Q)→P)→P in ¬/∧ form — the classic insertion-requiring theorem.
    // Phase 1 must exhaust its (small, strictly-shrinking) space without a
    // solve; phase 2 then either solves with the full alphabet or returns
    // the deepest fully-exhausted depth. Tiny fuel keeps this test fast.
    const peirce = formulaToDiagram('∀P Q:o. ¬(¬(¬(P ∧ ¬Q) ∧ ¬P) ∧ ¬P)')
    const outcome = minimalProofSearch(peirce, 200)
    if (outcome.status === 'solved') {
      expect(outcome.mode).toBe('full')
      expect(outcome.requires).toContain('spawn')
    } else {
      expect(outcome.requiresInsertion).toBe(true)
      expect(outcome.noProofWithin).toBeGreaterThanOrEqual(0)
    }
  })
  it('solves small generated problems from both families end to end', () => {
    const shrink = propShrinkFamily.generate({ atoms: 1, sampleSize: 6, minSize: 2, attempts: 10_000 }, seededRng(5))
    const shrinkOutcome = minimalProofSearch(shrink.diagram, DEFAULT_SEARCH_FUEL)
    expect(shrinkOutcome.status).toBe('solved')
    const walk = propWalkFamily.generate({ atoms: 1, length: 4, attempts: 500 }, seededRng(6))
    const walkOutcome = minimalProofSearch(walk.diagram, DEFAULT_SEARCH_FUEL)
    if (walkOutcome.status === 'solved' && walk.walkUpperBound !== undefined) {
      expect(walkOutcome.length).toBeLessThanOrEqual(walk.walkUpperBound + 5)
    } else {
      expect(walkOutcome.status).toBe('solved')
    }
  })
})
```

**If the first test reports a length other than 5:** do NOT change the expectation to match. Print `outcome.steps`, replay them by hand against the diagram, and understand the shorter (or longer) proof. If a genuinely shorter proof exists, the spec's hand count was wrong: update the spec's Testing section with the corrected derivation, then the test. If the search misses the 5-step proof, the enumerator or memoization is buggy — fix that. **If phase 1 solves Peirce's law**, the hand analysis (and a century of existential-graphs folklore) says something is wrong with the deletion-only alphabet's boundaries — investigate the found `steps` before touching the test. **If the seeded family cases in the third test come back `exhausted`**, the seed produced an insertion-requiring theorem; pick the nearest seed whose problem is deletion-solvable (verify by observation, note the choice in a comment).

- [ ] **Step 2: Run it, verify failure.**
- [ ] **Step 3: Implement**

```ts
// src/generate/search/digest.ts
import type { Diagram } from '../../kernel/diagram/diagram'
import { cutDepth } from '../../kernel/diagram'
import { sigKey } from '../../kernel/diagram/sig'

/**
 * Iso-invariant bucketing digest: multisets of region depths, node
 * kind/arity/sig at region depth, and wire sig with endpoint count — all
 * preserved by any diagram isomorphism. Two isomorphic diagrams always get
 * equal digests; unequal diagrams may collide, which is why the memo
 * confirms bucket membership with sameDiagram before pruning.
 */
export function diagramDigest(diagram: Diagram): string {
  const regionDepths = Object.keys(diagram.regions).map((id) => cutDepth(diagram, id)).sort((a, b) => a - b)
  const nodeKeys = Object.values(diagram.nodes)
    .map((node) => `${node.kind}:${node.kind === 'identity' ? node.arity : ''}:${sigKey(node.sig)}@${cutDepth(diagram, node.region)}`)
    .sort()
  const wireKeys = Object.values(diagram.wires)
    .map((wire) => `${sigKey(wire.sig)}#${wire.endpoints.length}`)
    .sort()
  return `${regionDepths.join(',')}|${nodeKeys.join(',')}|${wireKeys.join(',')}`
}
```

```ts
// src/generate/search/search.ts
import type { Diagram } from '../../kernel/diagram/diagram'
import { sameDiagram } from '../../kernel/diagram'
import { applyStep, EMPTY_PROOF_CONTEXT, ProofError, type ProofStep } from '../../kernel/proof'
import { RuleError } from '../../kernel/rules'
import { enumerateMoves, type CandidateMove, type MoveClass } from '../moves'
import { diagramDigest } from './digest'

export type SearchOutcome =
  | {
      readonly status: 'solved'
      /** Which alphabet the minimum is over: phase 1 (deletions only) or
       *  phase 2 (the full atomic alphabet). */
      readonly mode: 'deletion-only' | 'full'
      readonly length: number
      /** Classes proven to appear in every minimal-length proof. */
      readonly requires: readonly MoveClass[]
      readonly steps: readonly ProofStep[]
    }
  | {
      /** Phase 1 proved insertion is required, and phase 2's fuel ran out.
       *  `noProofWithin` is the deepest FULLY exhausted depth: the honest
       *  claim is "no proof of ≤ noProofWithin moves exists". */
      readonly status: 'exhausted'
      readonly requiresInsertion: true
      readonly noProofWithin: number
    }

/** Default phase-2 expanded-state budget. Sized by
 *  tests/generate/search.test.ts within the ordinary suite's 5s timeout.
 *  Raise or lower it THERE, observing both constraints. Phase 1 needs no
 *  fuel — its alphabet strictly shrinks the diagram. */
export const DEFAULT_SEARCH_FUEL = 20_000

const ALL_CLASSES: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration', 'vacuity'])

const DELETION_RULES = new Set(['erasure', 'deiteration', 'doubleCutElim'])

function isDeletionMove(candidate: CandidateMove): boolean {
  if (DELETION_RULES.has(candidate.step.rule)) return true
  return candidate.step.rule === 'vacuity' && candidate.step.direction === 'delete'
}

/** Phase-1 invariant guard: every deletion move strictly shrinks the
 *  diagram, so the reachable space is finite and small. Reaching this many
 *  states means that invariant broke — a bug, so crash loudly. */
const DELETION_STATE_GUARD = 1_000_000

class FuelExhausted extends Error {
  constructor() {
    super('minimal-proof search: fuel exhausted')
  }
}

function isBlank(diagram: Diagram): boolean {
  return Object.keys(diagram.regions).length === 1
    && Object.keys(diagram.nodes).length === 0
    && Object.keys(diagram.wires).length === 0
}

type MemoEntry = { readonly diagram: Diagram; bestRemaining: number }

class DiagramMemo {
  readonly #buckets = new Map<string, MemoEntry[]>()

  /** True if an isomorphic diagram was already visited with at least as much
   *  remaining depth; otherwise records this visit. Exact, never
   *  hash-optimistic: bucket membership is confirmed by sameDiagram. */
  visitedAtLeast(diagram: Diagram, remaining: number): boolean {
    const digest = diagramDigest(diagram)
    let bucket = this.#buckets.get(digest)
    if (bucket === undefined) {
      bucket = []
      this.#buckets.set(digest, bucket)
    }
    for (const entry of bucket) {
      if (sameDiagram(entry.diagram, diagram)) {
        if (entry.bestRemaining >= remaining) return true
        entry.bestRemaining = remaining
        return false
      }
    }
    bucket.push({ diagram, bestRemaining: remaining })
    return false
  }
}

/** Apply a candidate backward; a rule/proof refusal withdraws it (the
 *  enumerator mirrors gates, the applier is the authority); anything else
 *  is a genuine bug and propagates. */
function applyCandidate(diagram: Diagram, step: ProofStep): Diagram | null {
  try {
    return applyStep(diagram, step, EMPTY_PROOF_CONTEXT, 'backward')
  } catch (error) {
    if (error instanceof RuleError || error instanceof ProofError) return null
    throw error
  }
}

/**
 * Phase 1: complete BFS over the deletion-only alphabet. Returns a minimal
 * step sequence, or null when the entire (finite) space is exhausted —
 * which PROVES no deletion-only proof exists. `excluded` removes one move
 * class for the requirement probes.
 */
function deletionSearch(start: Diagram, excluded: MoveClass | null): ProofStep[] | null {
  const memo = new DiagramMemo()
  memo.visitedAtLeast(start, 0)
  let frontier: { diagram: Diagram; path: readonly ProofStep[] }[] = [{ diagram: start, path: [] }]
  let states = 1
  while (frontier.length > 0) {
    const next: typeof frontier = []
    for (const { diagram, path } of frontier) {
      if (isBlank(diagram)) return [...path]
      for (const candidate of enumerateMoves(diagram, 'backward', ALL_CLASSES)) {
        if (!isDeletionMove(candidate)) continue
        if (excluded !== null && candidate.moveClass === excluded) continue
        const applied = applyCandidate(diagram, candidate.step)
        if (applied === null) continue
        if (memo.visitedAtLeast(applied, 0)) continue
        states += 1
        if (states > DELETION_STATE_GUARD) {
          throw new Error('deletionSearch: state guard exceeded — the strictly-shrinking invariant is broken')
        }
        next.push({ diagram: applied, path: [...path, candidate.step] })
      }
    }
    frontier = next
  }
  return null
}

type Budget = { remaining: number }

function dfs(
  diagram: Diagram,
  remaining: number,
  classes: ReadonlySet<MoveClass>,
  memo: DiagramMemo,
  budget: Budget,
  trail: ProofStep[],
): boolean {
  if (isBlank(diagram)) return true
  if (remaining === 0) return false
  if (memo.visitedAtLeast(diagram, remaining)) return false
  if (budget.remaining <= 0) throw new FuelExhausted()
  budget.remaining -= 1
  for (const candidate of enumerateMoves(diagram, 'backward', classes)) {
    const next = applyCandidate(diagram, candidate.step)
    if (next === null) continue
    trail.push(candidate.step)
    if (dfs(next, remaining - 1, classes, memo, budget, trail)) return true
    trail.pop()
  }
  return false
}

function solveAtDepth(
  start: Diagram,
  depth: number,
  classes: ReadonlySet<MoveClass>,
  budget: Budget,
): ProofStep[] | null {
  const trail: ProofStep[] = []
  return dfs(start, depth, classes, new DiagramMemo(), budget, trail) ? trail : null
}

export function minimalProofSearch(start: Diagram, fuel: number): SearchOutcome {
  if (!Number.isInteger(fuel) || fuel < 1) throw new Error(`minimalProofSearch: bad fuel ${fuel}`)

  // Phase 1: complete deletion-only search.
  const deletionSteps = deletionSearch(start, null)
  if (deletionSteps !== null) {
    const requires: MoveClass[] = []
    for (const probe of ['iteration', 'doubleCut'] as const) {
      const without = deletionSearch(start, probe)
      // No proof at all — or none as short as the minimum — without the
      // class means every minimal proof uses it.
      if (without === null || without.length > deletionSteps.length) requires.push(probe)
    }
    return { status: 'solved', mode: 'deletion-only', length: deletionSteps.length, requires, steps: deletionSteps }
  }

  // Phase 2: insertion is PROVEN required; full alphabet under fuel.
  const budget: Budget = { remaining: fuel }
  for (let depth = 0; ; depth += 1) {
    let steps: ProofStep[] | null
    try {
      steps = solveAtDepth(start, depth, ALL_CLASSES, budget)
    } catch (error) {
      if (error instanceof FuelExhausted) {
        return { status: 'exhausted', requiresInsertion: true, noProofWithin: depth - 1 }
      }
      throw error
    }
    if (steps === null) continue
    const requires: MoveClass[] = ['spawn'] // proven by phase 1's exhaustion
    for (const excluded of ['iteration', 'doubleCut'] as const) {
      const reduced = new Set(ALL_CLASSES)
      reduced.delete(excluded)
      try {
        // Fresh budget per requirement probe: the probe is depth-capped at
        // the found length, so it is strictly smaller than the main search.
        if (solveAtDepth(start, depth, reduced, { remaining: fuel }) === null) requires.push(excluded)
      } catch (error) {
        // Probe exhausted: the requirement is UNPROVEN — omit it (the
        // `requires` list only ever contains proven requirements).
        if (!(error instanceof FuelExhausted)) throw error
      }
    }
    return { status: 'solved', mode: 'full', length: depth, requires, steps }
  }
}
```

- [ ] **Step 4: Run the test, verify it passes** (see the discrepancy protocol under Step 1). Watch the wall clock: each test must finish inside 5s. If the 5-step case is slow, the usual culprit is re-enumerating moves per dfs node on large intermediate diagrams — confirm the memo is actually pruning (`visitedAtLeast` hit rate) before touching anything else. `npm run typecheck`.
- [ ] **Step 5: Commit** — `git add src/generate/search tests/generate/search.test.ts && git commit -m "add backward minimal-proof search with honest bounds"`

---

### Task 9: UI panel

**Files:**
- Create: `src/app/generate-entry.ts`
- Create: `tests/app/helpers/fake-dom.ts` (extracted from `tests/app/formula-entry.test.ts`)
- Modify: `tests/app/formula-entry.test.ts` (import the extracted harness instead of defining it inline)
- Test: `tests/app/generate-entry.test.ts`

**Interfaces:**
- Consumes: `GENERATOR_FAMILIES`, `GeneratedProblem` (Task 4/7); `minimalProofSearch`, `DEFAULT_SEARCH_FUEL` (Task 8); `seededRng` (Task 1).
- Produces: `mountGenerateEntry(host: HTMLElement, commit: (diagram: Diagram) => void): MountedGenerateEntry` where `MountedGenerateEntry = { root; open(opener); close(); deactivate(); dispose() }` — the same lifecycle contract as `mountFormulaEntry` (`src/app/formula-entry.ts:4-10`), which Task 10's shell wiring relies on.

- [ ] **Step 1: Extract the fake-DOM harness.** Move the `TestElement`/`TestDocument` classes (and any sibling helpers defined at the top of `tests/app/formula-entry.test.ts`) verbatim into `tests/app/helpers/fake-dom.ts`, exporting each; update `tests/app/formula-entry.test.ts` to import them. Run `npx vitest run --config vitest.config.ts tests/app/formula-entry.test.ts` — it must still pass before continuing. Commit this refactor separately: `git add tests/app/helpers/fake-dom.ts tests/app/formula-entry.test.ts && git commit -m "extract fake-dom test harness"`.

- [ ] **Step 2: Write the failing test.** Model setup/teardown on the (now-refactored) `formula-entry.test.ts`. The behaviors to cover — write one `it` per line, driving the fake DOM exactly the way the formula-entry test does (createElement interception, dispatched `Event`s, reading `textContent`/`hidden`):

```ts
// tests/app/generate-entry.test.ts — assertions to implement with the harness:
// 1. mount renders a hidden dialog with a family <select> listing
//    GENERATOR_FAMILIES labels in order, knob inputs for the FIRST family
//    (one number input per KnobSpec, value = String(knob.default),
//    min = String(knob.min)), and a search-fuel input with value
//    String(DEFAULT_SEARCH_FUEL).
// 2. changing the select to 'prop-walk' re-renders the knob inputs to that
//    family's knobs (labels 'Atoms', 'Walk length', 'Attempt cap').
// 3. open() unhides and focuses; Escape closes and restores opener focus;
//    close()/deactivate()/dispose() mirror formula-entry semantics.
// 4. clicking Generate with tiny knobs (set atoms=1, sampleSize=6,
//    minSize=2 via the inputs) calls the family, then shows a non-empty
//    statement beginning '∀' and a difficulty line (either 'minimal proof:'
//    or 'no proof within'); Create diagram then invokes commit with the
//    generated diagram and closes the panel.
// 5. Create diagram is disabled (or errors visibly) before any generation.
// 6. a knob input holding an invalid value (e.g. atoms=0) surfaces the
//    readKnobs error in the role=alert output instead of throwing.
```

Determinism note: the panel seeds its RNG via `crypto.getRandomValues` — in the test, inject determinism by passing an options argument `{ rng?: () => number }` to `mountGenerateEntry` (the test passes `seededRng(1)`, the shell omits it). This injection point is part of the produced interface.

- [ ] **Step 3: Run it, verify failure.**
- [ ] **Step 4: Implement `src/app/generate-entry.ts`.** Mirror `formula-entry.ts` structurally (same class names `vpa-formula-entry`, `vpa-formula-actions`, `vpa-formula-error` so the existing CSS applies; same `role="dialog"`, Escape handling, `output role=alert`, opener-focus restore, `dispose` removing every listener). Differences:

```ts
// Shape (follow formula-entry.ts for the DOM/lifecycle boilerplate):
import { GENERATOR_FAMILIES } from '../generate'
import { DEFAULT_SEARCH_FUEL, minimalProofSearch } from '../generate/search/search'
import { seededRng } from '../generate/rng'
import type { Diagram } from '../kernel/diagram/diagram'
import type { GeneratedProblem } from '../generate'

export type MountedGenerateEntry = {
  readonly root: HTMLElement
  open(opener: HTMLElement): void
  close(): void
  deactivate(): void
  dispose(): void
}

const CLASS_LABELS: Readonly<Record<string, string>> = {
  spawn: 'insertion',
  iteration: 'iteration/deiteration',
  doubleCut: 'double cuts',
}

export function mountGenerateEntry(
  host: HTMLElement,
  commit: (diagram: Diagram) => void,
  options: { rng?: () => number } = {},
): MountedGenerateEntry {
  // ... DOM as in formula-entry.ts, with:
  // - <select> of families; on 'change', rebuild the knob inputs container
  //   from the selected family's knobs (label + <input type="number"
  //   min=String(knob.min) step="1" value=String(knob.default)>).
  // - a search-fuel <input type="number" min="1" value=String(DEFAULT_SEARCH_FUEL)>.
  // - Generate button (type="button"): read knobs (Number(input.value)),
  //   build rng = options.rng ?? freshCryptoRng(), call
  //   family.generate(params, rng) then minimalProofSearch(problem.diagram,
  //   fuel); render statement + difficulty; keep `current: GeneratedProblem
  //   | null`. All in try/catch rendering the error message into the alert
  //   output (textContent = message) — knob errors and generator attempt-cap
  //   errors are user-facing states here, not crashes.
  // - Create diagram (submit): if current === null, show 'generate a problem
  //   first' in the alert output; else commit(current.diagram) and close.
  // Difficulty rendering:
  //   solved (mode 'deletion-only') → `minimal proof: ${length} moves (deletions only)`
  //   solved (mode 'full')          → `minimal proof: ${length} moves`
  //   either solved form appends
  //     (requires.length ? ` · requires ${requires.map((c) => CLASS_LABELS[c] ?? c).join(', ')}` : '')
  //   exhausted → `requires insertion · no proof within ${noProofWithin} moves (search fuel exhausted)` +
  //               (walkUpperBound !== undefined ? ` · provable in ${walkUpperBound}` : '')
}

function freshCryptoRng(): () => number {
  const seedArray = new Uint32Array(1)
  crypto.getRandomValues(seedArray)
  return seededRng(seedArray[0]!)
}
```

- [ ] **Step 5: Run the test, verify it passes.** Run the full app suite too: `npx vitest run --config vitest.config.ts tests/app`. `npm run typecheck`.
- [ ] **Step 6: Commit** — `git add src/app/generate-entry.ts tests/app/generate-entry.test.ts && git commit -m "add random-problem generation panel"`

---

### Task 10: Shell wiring + e2e

**Files:**
- Modify: `src/app/shell.ts` — four touch points, mirroring `formulaEntry`/`formulaBtn` exactly:
  1. next to the `mountFormulaEntry` call (`shell.ts` ~line 683): `const generateEntry = mountGenerateEntry(document.body, (diagram) => { requireEdit(); pushEdit(diagram) })`
  2. next to `formulaBtn` (~line 1334): `let randomBtn!: HTMLButtonElement; randomBtn = button('Random…', () => generateEntry.open(randomBtn))`, appended into `compass.lifecycle` beside `formulaBtn`
  3. in `refreshChrome` beside `formulaBtn.hidden` (~line 971): `randomBtn.hidden = mode !== 'edit'` and `if (mode !== 'edit') generateEntry.deactivate()`
  4. in the dispose path beside `formulaEntry.dispose()` (~line 1698): `generateEntry.deactivate(); generateEntry.dispose()`
- Create: `e2e/random-problem.spec.ts`

**Interfaces:**
- Consumes: Task 9's `mountGenerateEntry` and the existing shell internals named above.

- [ ] **Step 1: Write the failing e2e test**

```ts
// e2e/random-problem.spec.ts
import { expect, test } from './zero-signature-fixture'

test('generate a random problem and start a backward proof on it', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  await page.getByRole('button', { name: /Mode: Edit/u }).click()
  const randomButton = page.getByRole('button', { name: 'Random…', exact: true })
  await randomButton.click()

  const dialog = page.getByRole('dialog')
  await expect(dialog).toBeVisible()
  // Small knobs so generation + search finish fast and deterministically enough.
  await dialog.getByLabel('Atoms').fill('1')
  await dialog.getByLabel('Sample connectives').fill('6')
  await dialog.getByLabel('Minimum core connectives').fill('2')
  await dialog.getByRole('button', { name: 'Generate', exact: true }).click()
  await expect(dialog).toContainText('∀')
  await expect(dialog).toContainText(/minimal proof:|no proof within/u)

  await dialog.getByRole('button', { name: 'Create diagram', exact: true }).click()
  await expect(dialog).toBeHidden()
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBeGreaterThan(0)

  await page.getByRole('button', { name: /Mode: Edit/u }).click()
  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  await expect(page.locator('#status')).toContainText('PROVE')
})
```

Before running, read `e2e/app.spec.ts` end to end for the fixture's conventions (mode-button toggling, `#status` semantics) and adjust selectors to what the app actually renders — by observation, not by loosening assertions. Knob inputs need `aria-label` or `<label htmlFor>` in the panel for `getByLabel` to work; Task 9's implementation must have provided them (fix the panel if not).

- [ ] **Step 2: Run it, verify failure** — `npx playwright test e2e/random-problem.spec.ts` (the `pree2e` hook emits theories automatically). Expected: the Random… button does not exist yet.
- [ ] **Step 3: Wire the shell** (the four touch points above).
- [ ] **Step 4: Run the e2e test, verify it passes.** Then the full gates: `npm run typecheck && npm test && npx playwright test`. Every suite green — a single failure anywhere means the task is not done.
- [ ] **Step 5: Commit** — `git add src/app/shell.ts e2e/random-problem.spec.ts && git commit -m "wire random-problem mode into the shell"`

---

## Completion checklist (run after Task 10)

- [ ] `npm run typecheck` — clean.
- [ ] `npm test` — every test green, including the pre-existing suites.
- [ ] `npx playwright test` — green.
- [ ] `npm run formal:size` — clean.
- [ ] Launch the app (`npm run app`, background) and generate one problem from each family by hand; confirm the statement renders, the difficulty line appears, Create diagram lands it in edit mode, and Prove backward starts on it. This is the real deliverable — observe it working before reporting done.
