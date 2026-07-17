import type { Diagram } from '../kernel/diagram/diagram'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import type { PuzzleDefinition, TeacherIntervention } from './types'

export type TeacherSignal =
  | { readonly kind: 'opening' }
  | { readonly kind: 'completion' }
  | { readonly kind: 'recognizedUnwinnable'; readonly diagram: Diagram }

export type TeacherPresentationIntent =
  | { readonly kind: 'modalInstruction' }
  | { readonly kind: 'nonblockingCommentary'; readonly recovery: 'timeline' }
  | { readonly kind: 'completionCommentary' }

export type PresentedTeacherIntervention = {
  readonly intervention: TeacherIntervention
  readonly presentation: TeacherPresentationIntent
}

const presentationFor = (intervention: TeacherIntervention): TeacherPresentationIntent => {
  switch (intervention.trigger.kind) {
    case 'opening': return { kind: 'modalInstruction' }
    case 'recognizedUnwinnable': {
      return { kind: 'nonblockingCommentary', recovery: 'timeline' }
    }
    case 'completion': return { kind: 'completionCommentary' }
  }
}

export function teacherInterventionsFor(
  puzzle: PuzzleDefinition,
  signal: TeacherSignal,
  seen: ReadonlySet<string>,
): readonly PresentedTeacherIntervention[] {
  return puzzle.teacher.flatMap((intervention) => {
    if (intervention.repeat === 'once' && seen.has(intervention.id)) return []
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
    return matches ? [{ intervention, presentation: presentationFor(intervention) }] : []
  })
}
