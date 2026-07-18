import type { Diagram } from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import {
  guidanceDeliveryIdentity,
  isGuidanceDelivered,
  type PuzzleDefinition,
  type GuidanceDeliveryIdentity,
  type TeacherIntervention,
} from './types'

export type TeacherSignal =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | { readonly kind: 'recognizedUnwinnable'; readonly diagram: Diagram }

export type PresentedGuidanceIntervention = {
  readonly identity: GuidanceDeliveryIdentity
  readonly intervention: TeacherIntervention
}

export function guidanceInterventionsFor(
  puzzle: PuzzleDefinition,
  signal: TeacherSignal,
  delivered: readonly GuidanceDeliveryIdentity[],
): readonly PresentedGuidanceIntervention[] {
  return puzzle.teacher.flatMap((intervention) => {
    const identity = guidanceDeliveryIdentity(puzzle.id, intervention.id)
    if (intervention.repeat === 'once' && isGuidanceDelivered(delivered, identity)) return []
    const trigger = intervention.trigger
    if (trigger.kind !== signal.kind) return []
    let matches: boolean
    switch (trigger.kind) {
      case 'opening':
      case 'completion': matches = true; break
      case 'recognizedUnwinnable':
        matches = signal.kind === 'recognizedUnwinnable'
          && exploreForm(trigger.state.diagram) === exploreForm(signal.diagram)
    }
    return matches ? [{ identity, intervention }] : []
  })
}
