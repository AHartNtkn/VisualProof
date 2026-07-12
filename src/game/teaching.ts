import type { Diagram } from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import type { PuzzleDefinition, TeacherIntervention } from './types'

export type TeacherSignal =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | { readonly kind: 'stalled'; readonly level: 1 | 2 | 3 }
  | { readonly kind: 'proofState'; readonly diagram: Diagram }

export function teacherInterventionsFor(
  puzzle: PuzzleDefinition,
  signal: TeacherSignal,
  seen: ReadonlySet<string>,
): readonly TeacherIntervention[] {
  return puzzle.teacher.filter((intervention) => {
    if (intervention.repeat === 'once' && seen.has(intervention.id)) return false
    const trigger = intervention.trigger
    if (trigger.kind !== signal.kind) return false
    switch (trigger.kind) {
      case 'opening':
      case 'completion': return true
      case 'stalled': return signal.kind === 'stalled' && trigger.level === signal.level
      case 'proofState':
        return signal.kind === 'proofState'
          && exploreForm(trigger.state.diagram) === exploreForm(signal.diagram)
    }
  })
}
