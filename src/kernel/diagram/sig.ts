/**
 * Signature grammar for wires (replaces second-order quantifier "bubbles").
 *
 * A Sig is a recursive structure representing the shape of a wire's type:
 * - TERM (ι): a simple individual
 * - REL: a relation with a fixed arity, structurally defined by its argument signatures
 */

export type Sig = { readonly kind: 'term' } | { readonly kind: 'rel'; readonly args: readonly Sig[] }

export type RelSig = Extract<Sig, { kind: 'rel' }>

export class SigError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'SigError'
  }
}

/**
 * Shared immutable value for the term signature (ι).
 */
export const TERM: Sig = Object.freeze({ kind: 'term' })

/**
 * Construct a relation signature with the given argument signatures.
 * @param args the argument signatures defining the relation's shape
 * @returns a RelSig value
 */
export function relSig(args: readonly Sig[]): RelSig {
  return Object.freeze({ kind: 'rel', args: Object.freeze(args) })
}

/**
 * Structural equality test for signatures.
 * Two signatures are equal if they have the same structure recursively.
 * @param a first signature
 * @param b second signature
 * @returns true if structurally equal, false otherwise
 */
export function sigEquals(a: Sig, b: Sig): boolean {
  if (a.kind !== b.kind) return false

  if (a.kind === 'term') {
    return true
  }

  // Both are 'rel'
  const relA = a as RelSig
  const relB = b as RelSig

  if (relA.args.length !== relB.args.length) return false

  for (let i = 0; i < relA.args.length; i++) {
    const argA = relA.args[i]
    const argB = relB.args[i]
    if (argA === undefined || argB === undefined || !sigEquals(argA, argB)) return false
  }

  return true
}

/**
 * Canonical injective string representation of a signature.
 * - TERM maps to 't'
 * - REL maps to '(' + args.map(sigKey).join(',') + ')'
 *
 * This representation is injective: different signatures produce different strings.
 * @param s the signature
 * @returns canonical string key
 */
export function sigKey(s: Sig): string {
  if (s.kind === 'term') {
    return 't'
  }

  // s.kind === 'rel'
  const relS = s as RelSig
  const argKeys = relS.args.map(sigKey)
  return '(' + argKeys.join(',') + ')'
}

/**
 * Order (depth) of a signature.
 * - TERM has order 0
 * - REL has order 1 + max(0, ...args.map(sigOrder))
 *
 * This represents the nesting depth of relation constructors.
 * @param s the signature
 * @returns order (depth) as a non-negative integer
 */
export function sigOrder(s: Sig): number {
  if (s.kind === 'term') {
    return 0
  }

  // s.kind === 'rel'
  const relS = s as RelSig

  if (relS.args.length === 0) {
    return 1
  }

  let maxArgOrder = 0
  for (const arg of relS.args) {
    const argOrder = sigOrder(arg)
    if (argOrder > maxArgOrder) {
      maxArgOrder = argOrder
    }
  }
  return 1 + maxArgOrder
}

/**
 * Type guard that validates a value is a well-formed Sig.
 * Throws SigError loudly with specific details if malformed.
 *
 * @param s unknown value to validate
 * @throws SigError if s is not a valid Sig
 */
export function assertWellFormedSig(s: unknown): asserts s is Sig {
  if (typeof s !== 'object' || s === null) {
    throw new SigError(
      `Invalid signature: expected an object, got ${typeof s === 'object' ? 'null' : typeof s}`,
    )
  }

  const obj = s as Record<string, unknown>

  if (!('kind' in obj)) {
    throw new SigError('Invalid signature: missing "kind" property')
  }

  const kind = obj.kind

  if (kind !== 'term' && kind !== 'rel') {
    throw new SigError(
      `Invalid signature: "kind" must be "term" or "rel", got "${String(kind)}"`,
    )
  }

  if (kind === 'term') {
    // Term signatures are valid if they have kind: 'term'
    return
  }

  // kind === 'rel'
  if (!('args' in obj)) {
    throw new SigError('Invalid signature: rel signature missing "args" property')
  }

  const args = obj.args

  if (!Array.isArray(args)) {
    throw new SigError(
      `Invalid signature: rel "args" must be an array, got ${typeof args}`,
    )
  }

  // Validate each argument is a well-formed Sig
  for (let i = 0; i < args.length; i++) {
    const arg = args[i]
    try {
      assertWellFormedSig(arg)
    } catch (e) {
      throw new SigError(
        `Invalid signature: rel "args[${i}]" is malformed: ${(e as Error).message}`,
      )
    }
  }
}
