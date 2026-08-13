/** Proof-layer failures: replay errors, theorem-check failures, meet mismatches. */
export class ProofError extends Error {
  constructor(message: string, options?: ErrorOptions) {
    super(message, options)
    this.name = 'ProofError'
  }
}
