import type { GameProgress } from './model'
import {
  openingTutorialContent,
  type LiveTutorialContent,
  type VisibleTutorialMilestoneId,
} from './tutorial/content'

export type TutorialMilestoneId =
  | 'move'
  | 'look'
  | 'ascend'
  | 'descend'
  | 'sprint'
  | 'select-tree'
  | 'move-orbit'
  | 'exit-orbit'
  | 'spawn-two-sprouts'
  | 'acquire-double-cut'
  | 'apply-double-cut'
  | 'double-cut-explained'
  | 'acquire-iteration'
  | 'duplicate-nonblank'
  | 'iterate-within-tree'
  | 'complete-blank-order'
  | 'complete-single-double-cut-order'
  | 'complete-irregular-double-cut-a-order'
  | 'complete-irregular-double-cut-b-order'

export type TutorialEvent =
  | { readonly kind: 'camera-capability'; readonly capability: 'move' | 'look' | 'ascend' | 'descend' | 'sprint' }
  | { readonly kind: 'tree-selected' }
  | { readonly kind: 'orbit-moved' }
  | { readonly kind: 'orbit-exited' }
  | { readonly kind: 'sprout-spawned'; readonly blankTreeCount: number }
  | { readonly kind: 'tool-acquired'; readonly toolId: string }
  | { readonly kind: 'double-cut-applied' }
  | { readonly kind: 'ledger-opened' }
  | { readonly kind: 'nonblank-tree-duplicated' }
  | { readonly kind: 'same-tree-iteration-applied' }
  | { readonly kind: 'order-completed'; readonly orderId: string }

export type TutorialInstruction = {
  readonly milestoneId: VisibleTutorialMilestoneId
  readonly text: string
}

export type TutorialCommit = {
  readonly newlyCompleted: readonly TutorialMilestoneId[]
  readonly instruction: TutorialInstruction | null
}

type TutorialMilestone = {
  readonly milestoneId: TutorialMilestoneId
  readonly prerequisites: readonly TutorialMilestoneId[]
  readonly recognitionPrerequisites: readonly TutorialMilestoneId[]
  readonly matches: (event: TutorialEvent) => boolean
  readonly visible: boolean
}

const milestones: readonly TutorialMilestone[] = [
  capabilityMilestone('move', []),
  capabilityMilestone('look', ['move']),
  capabilityMilestone('ascend', ['look']),
  capabilityMilestone('descend', ['ascend']),
  capabilityMilestone('sprint', ['descend']),
  milestone('select-tree', ['sprint'], (event) => event.kind === 'tree-selected'),
  milestone('move-orbit', ['select-tree'], (event) => event.kind === 'orbit-moved'),
  milestone('exit-orbit', ['move-orbit'], (event) => event.kind === 'orbit-exited'),
  milestone('spawn-two-sprouts', ['exit-orbit'], (event) => (
    event.kind === 'sprout-spawned' && event.blankTreeCount >= 3
  )),
  milestone('acquire-double-cut', ['spawn-two-sprouts'], (event) => (
    event.kind === 'tool-acquired' && event.toolId === 'double-cut'
  )),
  milestone('apply-double-cut', ['acquire-double-cut'], (event) => event.kind === 'double-cut-applied'),
  milestone(
    'double-cut-explained',
    ['apply-double-cut'],
    (event) => event.kind === 'ledger-opened',
    ['apply-double-cut'],
  ),
  milestone('acquire-iteration', ['double-cut-explained'], (event) => (
    event.kind === 'tool-acquired' && event.toolId === 'iteration'
  )),
  milestone('duplicate-nonblank', ['acquire-iteration'], (event) => event.kind === 'nonblank-tree-duplicated'),
  milestone(
    'iterate-within-tree',
    ['duplicate-nonblank'],
    (event) => event.kind === 'same-tree-iteration-applied',
    ['duplicate-nonblank'],
  ),
  milestone('complete-blank-order', ['iterate-within-tree'], (event) => (
    event.kind === 'order-completed' && event.orderId === 'blank-sprout'
  )),
  silentMilestone('complete-single-double-cut-order', ['complete-blank-order'], (event) => (
    event.kind === 'order-completed' && event.orderId === 'single-double-cut'
  )),
  silentMilestone('complete-irregular-double-cut-a-order', ['complete-single-double-cut-order'], (event) => (
    event.kind === 'order-completed' && event.orderId === 'irregular-double-cut-a'
  )),
  silentMilestone('complete-irregular-double-cut-b-order', ['complete-single-double-cut-order'], (event) => (
    event.kind === 'order-completed' && event.orderId === 'irregular-double-cut-b'
  )),
]

const milestoneIds = new Set<TutorialMilestoneId>(milestones.map(({ milestoneId }) => milestoneId))

export function toolTutorialGate(toolId: string): TutorialMilestoneId | null {
  switch (toolId) {
    case 'double-cut': return 'spawn-two-sprouts'
    case 'iteration': return 'double-cut-explained'
    default: return null
  }
}

export function orderTutorialGate(orderId: string): TutorialMilestoneId | null {
  return orderId === 'blank-sprout' ? 'iterate-within-tree' : null
}

export class TutorialSession {
  readonly #completed: Set<TutorialMilestoneId>
  #enabled: boolean

  public constructor(
    enabled = true,
    completed: Iterable<string> = [],
    private readonly content: LiveTutorialContent = openingTutorialContent,
  ) {
    this.#enabled = enabled
    this.#completed = new Set(
      [...completed].filter((milestoneId): milestoneId is TutorialMilestoneId => milestoneIds.has(milestoneId as TutorialMilestoneId)),
    )
  }

  public get enabled(): boolean {
    return this.#enabled
  }

  public get completed(): ReadonlySet<TutorialMilestoneId> {
    return this.#completed
  }

  public get currentInstruction(): TutorialInstruction | null {
    if (!this.#enabled) return null
    const next = milestones.find(({ milestoneId, visible }) => visible && !this.#completed.has(milestoneId))
    return next === undefined || !this.prerequisitesMet(next) ? null : instruction(next, this.content)
  }

  public setEnabled(enabled: boolean): void {
    this.#enabled = enabled
  }

  public check(milestoneId: TutorialMilestoneId): boolean {
    return !this.#enabled || this.#completed.has(milestoneId)
  }

  public observe(event: TutorialEvent): TutorialCommit {
    return this.commit(this.record([event]))
  }

  public reconcileDurableProgress(
    progress: Pick<GameProgress, 'acquiredToolIds' | 'orders'>,
  ): TutorialCommit {
    const events: TutorialEvent[] = []
    for (const toolId of progress.acquiredToolIds) {
      events.push({ kind: 'tool-acquired', toolId })
    }
    for (const [orderId, state] of progress.orders) {
      if (state.kind === 'completed') events.push({ kind: 'order-completed', orderId })
    }
    return this.commit(this.record(events))
  }

  private record(events: readonly TutorialEvent[]): readonly TutorialMilestoneId[] {
    const newlyCompleted: TutorialMilestoneId[] = []
    for (const milestone of milestones) {
      if (
        this.#completed.has(milestone.milestoneId)
        || !milestone.recognitionPrerequisites.every((prerequisite) => this.#completed.has(prerequisite))
        || !events.some((event) => milestone.matches(event))
      ) continue
      this.#completed.add(milestone.milestoneId)
      newlyCompleted.push(milestone.milestoneId)
    }
    return newlyCompleted
  }

  private commit(newlyCompleted: readonly TutorialMilestoneId[]): TutorialCommit {
    return { newlyCompleted, instruction: this.currentInstruction }
  }

  private prerequisitesMet(milestone: TutorialMilestone): boolean {
    return milestone.prerequisites.every((prerequisite) => this.#completed.has(prerequisite))
  }
}

function capabilityMilestone(
  milestoneId: Extract<TutorialMilestoneId, 'move' | 'look' | 'ascend' | 'descend' | 'sprint'>,
  prerequisites: readonly TutorialMilestoneId[],
): TutorialMilestone {
  return milestone(milestoneId, prerequisites, (event) => (
    event.kind === 'camera-capability' && event.capability === milestoneId
  ))
}

function milestone(
  milestoneId: TutorialMilestoneId,
  prerequisites: readonly TutorialMilestoneId[],
  matches: (event: TutorialEvent) => boolean,
  recognitionPrerequisites: readonly TutorialMilestoneId[] = [],
): TutorialMilestone {
  return { milestoneId, prerequisites, recognitionPrerequisites, matches, visible: true }
}

function silentMilestone(
  milestoneId: TutorialMilestoneId,
  prerequisites: readonly TutorialMilestoneId[],
  matches: (event: TutorialEvent) => boolean,
): TutorialMilestone {
  return { milestoneId, prerequisites, recognitionPrerequisites: [], matches, visible: false }
}

function instruction(milestone: TutorialMilestone, content: LiveTutorialContent): TutorialInstruction {
  if (!milestone.visible) throw new Error(`silent milestone '${milestone.milestoneId}' has no instruction`)
  return {
    milestoneId: milestone.milestoneId as VisibleTutorialMilestoneId,
    text: content.current.definition(milestone.milestoneId).text,
  }
}
