import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { GameDomainError } from './types'

const blank = new DiagramBuilder().build()
const blankForm = exploreForm(blank)

export function blankDiagram(): Diagram {
  return blank
}

export function isBlank(diagram: Diagram): boolean {
  return exploreForm(diagram) === blankForm
}

export function assertClosedGoal(goal: DiagramWithBoundary): void {
  if (goal.boundary.length !== 0) {
    throw new GameDomainError(`puzzle goal must be closed; received boundary arity ${goal.boundary.length}`)
  }
}
