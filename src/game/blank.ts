import { DiagramBuilder } from '../kernel/diagram/builder'
import type { Diagram } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { GameDomainError } from './types'

const blank = new DiagramBuilder().build()

export function blankDiagram(): Diagram {
  return blank
}

export function isBlank(diagram: Diagram): boolean {
  return diagram.regions[diagram.root]?.kind === 'sheet'
    && Object.keys(diagram.regions).length === 1
    && Object.keys(diagram.nodes).length === 0
    && Object.keys(diagram.wires).length === 0
}

export function assertClosedGoal(goal: DiagramWithBoundary): void {
  if (goal.boundary.length !== 0) {
    throw new GameDomainError(`puzzle goal must be closed; received boundary arity ${goal.boundary.length}`)
  }
}
