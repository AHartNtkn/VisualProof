/** Proof-layer failures: replay errors, theorem-check failures, meet mismatches. */
export class ProofError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'ProofError'
  }
}
