/** Rule-gate violations: a distinct vocabulary from structural DiagramError. */
export class RuleError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'RuleError'
  }
}
