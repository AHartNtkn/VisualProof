import { flattenAnd, isTautology, sameFormula, type PropFormula } from './formula'

const TOP: PropFormula = { kind: 'top' }
const BOT: PropFormula = { kind: 'bot' }

/**
 * Constant elimination (⊤∧φ≡φ, ⊥∧φ≡⊥, ¬⊤≡⊥, ¬⊥≡⊤), doubled-negation
 * collapse (¬¬ψ≡ψ), and ∧-idempotence dedup (φ∧φ≡φ, flattened so a
 * non-adjacent duplicate like A∧B∧A is caught too), bottom-up. The collapse
 * must live here rather than in the caller because constant elimination can
 * itself create a doubled negation (¬(⊤∧¬P) → ¬¬P), so by induction this
 * function's output is always ¬¬-free. Dedup runs on the flattened list
 * AFTER every member has been recursively simplified (so ¬¬A next to A
 * dedupes once the ¬¬ has collapsed), so by the same induction this
 * function's output never has duplicate ∧-siblings.
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
      const simplified = flattenAnd(formula).map(simplify)
      if (simplified.some((conjunct) => conjunct.kind === 'bot')) return BOT
      const deduped: PropFormula[] = []
      for (const conjunct of simplified) {
        if (conjunct.kind === 'top') continue
        if (deduped.some((kept) => sameFormula(kept, conjunct))) continue
        deduped.push(conjunct)
      }
      if (deduped.length === 0) return TOP
      return deduped.reduce((left, right) => ({ kind: 'and', left, right }))
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

/**
 * One pass of deiteration-redex removal, over a "current area" conjunct
 * list and its available justifier CONTEXT (deep-equal candidates drawn
 * from every enclosing area, not just this one). An item is a redex —
 * removable — when a structurally identical copy (`sameFormula`) is
 * available DISJOINTLY: in `context`, or as an earlier-kept sibling in this
 * same area. This is exactly Peirce's existential-graph deiteration
 * containment rule: the justifier's area must ENCLOSE (or equal) the
 * copy's area, crossing any number of cut boundaries in either direction —
 * unlike erasure/insertion, deiteration is not polarity-gated.
 *
 * Recursing into a kept item that is `not(body)` (a cut) extends the
 * context available to `body`'s own area with this area's OTHER kept
 * conjuncts (excluding the cut itself — a cut is never disjoint from its
 * own contents, so it can never justify a deiteration inside itself).
 */
function normalizeArea(items: readonly PropFormula[], context: readonly PropFormula[]): PropFormula[] {
  const kept: PropFormula[] = []
  for (const item of items) {
    const isRedex = context.some((candidate) => sameFormula(candidate, item))
      || kept.some((candidate) => sameFormula(candidate, item))
    if (!isRedex) kept.push(item)
  }
  return kept.map((item, index) => {
    if (item.kind !== 'not') return item
    const cutContext = [...context, ...kept.filter((_, other) => other !== index)]
    const newBodyItems = normalizeArea(flattenAnd(item.body), cutContext)
    const newBody = newBodyItems.length === 0
      ? TOP
      : newBodyItems.reduce((left, right) => ({ kind: 'and', left, right }))
    return { kind: 'not', body: newBody }
  })
}

/** One pass of `normalizeArea` over the whole formula, treated as a
 *  single-item top-level area with no inherited context (the sheet — an
 *  area nothing else encloses). */
export function normalizeDeiterations(formula: PropFormula): PropFormula {
  const normalized = normalizeArea(flattenAnd(formula), [])
  if (normalized.length === 0) return TOP
  return normalized.reduce((left, right) => ({ kind: 'and', left, right }))
}

/**
 * Loop normalizeDeiterations + simplify to a fixpoint. Termination: each
 * `normalizeArea` call only ever DROPS conjuncts (never adds), so a pass
 * that removes anything strictly reduces connectiveCount by at least the
 * dropped conjunct's own count plus one for the ∧-join it occupied; simplify
 * is separately non-increasing (Task 13). So every iteration either changes
 * `current` — strictly decreasing its non-negative connectiveCount — or is
 * the identity and the loop returns; the count is bounded below by 0.
 */
export function normalizeToFixpoint(formula: PropFormula): PropFormula {
  let current = simplify(formula)
  for (;;) {
    const next = simplify(normalizeDeiterations(current))
    if (sameFormula(next, current)) return current
    current = next
  }
}

/** True when one more normalize+simplify pass would still change the
 *  formula — a deiteration redex (same-area or ancestor-justified) remains
 *  somewhere. Generalizes the same-area-only `containsDuplicateConjunct`
 *  (prop/formula.ts) with ancestor-justified redexes too. Backs the
 *  `fullDeiteration`-ON backstop; the flag-off backstop uses
 *  `containsDuplicateConjunct` instead, since flag-off `shrinkToCore` never
 *  runs `normalizeToFixpoint` and so only guarantees the same-area case. */
export function containsDeiterationRedex(formula: PropFormula): boolean {
  return !sameFormula(normalizeToFixpoint(formula), formula)
}

/**
 * Greedy fixpoint, jointly normalizing two independent redex classes until
 * NEITHER fires: deiteration redexes (`normalizeToFixpoint`, ancestor- or
 * same-area-justified structural duplicates) and weakening-verified dead
 * weight (the original mechanism — substitute a occurrence with its
 * weakening constant, keep the substitution if the result is still a
 * tautology). Each can expose the other's redexes (a dead-weight conjunct
 * can be part of what makes a deiteration justifier available, and
 * removing a deiteration redex can strand a sibling as now-provably dead
 * weight), so they are interleaved rather than run once in sequence.
 * Termination: `normalizeToFixpoint` is itself non-increasing on
 * connectiveCount (see its own comment); a weakening substitution replaces
 * a subformula with a 0-connective constant, which — because the
 * substituted position is always the operand of an enclosing ∧-conjunct
 * slot or a `not`, both of which `simplify` collapses immediately when
 * their operand is a bare ⊤/⊥ — is always followed by at least one
 * connective's worth of simplification, so it too strictly decreases
 * connectiveCount whenever it fires. The outer loop only continues when one
 * of the two sub-steps actually changed `current`, so connectiveCount
 * (bounded below by 0) strictly decreases every iteration that continues.
 *
 * `fullDeiteration` gates whether the deiteration-normalization sub-step
 * runs at all (user ruling, opt-in default off — measured: its fixed
 * points are nearly unsamplable, 100% collapse to ⊤ across 18 knob
 * configurations at atoms 2–4, sample sizes 10–800). With it off, this is
 * exactly the original weakening-only loop (`simplify` still runs — the
 * always-on ¬¬/idempotence repairs live there, unconditionally).
 */
export function shrinkToCore(formula: PropFormula, atoms: number, fullDeiteration: boolean): PropFormula {
  if (!isTautology(formula, atoms)) throw new Error('shrinkToCore: input is not a tautology')
  let current = fullDeiteration ? normalizeToFixpoint(formula) : simplify(formula)
  for (;;) {
    if (fullDeiteration) {
      const normalized = normalizeToFixpoint(current)
      if (!sameFormula(normalized, current)) {
        current = normalized
        continue
      }
    }
    let weakened = false
    for (const candidate of weakenings(current)) {
      if (isTautology(candidate, atoms)) {
        current = simplify(candidate)
        weakened = true
        break
      }
    }
    if (weakened) continue
    break
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
