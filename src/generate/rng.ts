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
