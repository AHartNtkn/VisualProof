import type { Vec2 } from '../view/vec'

export const REFUSAL_LIFETIME_MS = 3_200

export type RefusalInput = {
  readonly text: string
  /** Client-space pointer coordinates at the instant the attempt failed. */
  readonly pointer: Vec2
}

export type RefusalNotice = RefusalInput & {
  readonly sequence: number
  readonly expiresAt: number
}

export type FieldProblem = {
  readonly id: string
  readonly text: string
}

export type FeedbackState = {
  readonly refusal: RefusalNotice | null
  readonly problems: readonly FieldProblem[]
}

/**
 * Error-only semantic authority. Successful actions and ordinary interaction
 * state never enter this controller; the resulting UI state is their complete
 * presentation. Field problems remain keyed state while one transient refusal
 * replaces the previous refusal.
 */
export class FeedbackController {
  #sequence = 0
  #refusal: RefusalNotice | null = null
  readonly #problems = new Map<string, FieldProblem>()
  readonly #now: () => number

  constructor(now: () => number = Date.now) {
    this.#now = now
  }

  refuse(input: RefusalInput): RefusalNotice {
    const refusal: RefusalNotice = {
      ...input,
      sequence: ++this.#sequence,
      expiresAt: this.#now() + REFUSAL_LIFETIME_MS,
    }
    this.#refusal = refusal
    return refusal
  }

  clearRefusal(sequence?: number): void {
    if (sequence === undefined || this.#refusal?.sequence === sequence) this.#refusal = null
  }

  setProblem(id: string, text: string): FieldProblem {
    const problem = { id, text }
    this.#problems.set(id, problem)
    return problem
  }

  clearProblem(id: string): void {
    this.#problems.delete(id)
  }

  snapshot(): FeedbackState {
    return { refusal: this.#refusal, problems: [...this.#problems.values()] }
  }
}
