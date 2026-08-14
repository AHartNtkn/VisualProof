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

/** True when the formula contains not(not(_)) anywhere — trivially
 *  removable structure the generators must never ship. */
export function containsDoubleNegation(formula: PropFormula): boolean {
  switch (formula.kind) {
    case 'atom':
    case 'top':
    case 'bot':
      return false
    case 'not':
      return formula.body.kind === 'not' || containsDoubleNegation(formula.body)
    case 'and':
      return containsDoubleNegation(formula.left) || containsDoubleNegation(formula.right)
  }
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
