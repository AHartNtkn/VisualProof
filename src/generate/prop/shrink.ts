import { isTautology, type PropFormula } from './formula'

const TOP: PropFormula = { kind: 'top' }
const BOT: PropFormula = { kind: 'bot' }

/**
 * Constant elimination (⊤∧φ≡φ, ⊥∧φ≡⊥, ¬⊤≡⊥, ¬⊥≡⊤) plus doubled-negation
 * collapse (¬¬ψ≡ψ), bottom-up. The collapse must live here rather than in
 * the caller because constant elimination can itself create a doubled
 * negation (¬(⊤∧¬P) → ¬¬P), so by induction this function's output is
 * always ¬¬-free.
 */
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
      if (body.kind === 'not') return body.body
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
