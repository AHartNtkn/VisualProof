import type { NodeId } from '../kernel/diagram/diagram'
import type { Vec2 } from '../view/vec'
import type { Hit } from './hittest'

export type FeedbackKind =
  | 'ambient'
  | 'guidance'
  | 'success'
  | 'refusal'
  | 'mode'
  | 'history'
  | 'problem'

export type FeedbackPersistence = 'transient' | 'interaction' | 'state' | 'problem'

export type FeedbackAnchor =
  | { readonly kind: 'selection'; readonly hits: readonly Hit[] }
  | { readonly kind: 'hit'; readonly hit: Hit }
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'point'; readonly point: Vec2 }
  | { readonly kind: 'control'; readonly id: string }
  | { readonly kind: 'viewport' }

export type FeedbackInput = {
  readonly kind: FeedbackKind
  readonly text: string
  readonly owner: FeedbackAnchor
  readonly persistence: FeedbackPersistence
  readonly affected?: readonly Hit[]
  readonly problemId?: string
}

export type FeedbackNotice = FeedbackInput & {
  readonly sequence: number
}

export type FeedbackState = {
  readonly current: FeedbackNotice | null
  readonly problems: readonly FeedbackNotice[]
}

/**
 * The single semantic authority for application feedback. Presentation may
 * retain a notice briefly for animation, but it may not invent event identity,
 * ownership, persistence, or problem lifetime outside this controller.
 */
export class FeedbackController {
  #sequence = 0
  #current: FeedbackNotice | null = null
  readonly #problems = new Map<string, FeedbackNotice>()

  report(input: FeedbackInput): FeedbackNotice {
    if (input.persistence === 'problem' && input.problemId === undefined) {
      throw new Error('persistent feedback requires a stable problemId')
    }
    if (input.persistence !== 'problem' && input.problemId !== undefined) {
      throw new Error('only persistent feedback may carry a problemId')
    }
    const notice: FeedbackNotice = { ...input, sequence: ++this.#sequence }
    this.#current = notice
    if (notice.problemId !== undefined) this.#problems.set(notice.problemId, notice)
    return notice
  }

  clearProblem(problemId: string): void {
    const removed = this.#problems.get(problemId)
    this.#problems.delete(problemId)
    if (removed !== undefined && this.#current?.sequence === removed.sequence) this.#current = null
  }

  clearInteraction(): void {
    if (this.#current?.persistence === 'interaction') this.#current = null
  }

  snapshot(): FeedbackState {
    return { current: this.#current, problems: [...this.#problems.values()] }
  }
}
