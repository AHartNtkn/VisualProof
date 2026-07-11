import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import type { RegionId } from '../../src/kernel/diagram/diagram'

export type VeilFixture = {
  readonly goal: DiagramWithBoundary
  readonly eliminations: readonly RegionId[]
}

export function twoVeils(): VeilFixture {
  const b = new DiagramBuilder()
  const outer = b.cut(b.root)
  b.cut(outer)
  return { goal: mkDiagramWithBoundary(b.build(), []), eliminations: [outer] }
}

export function fourVeils(): VeilFixture {
  const b = new DiagramBuilder()
  const outer = b.cut(b.root)
  const second = b.cut(outer)
  const third = b.cut(second)
  b.cut(third)
  return { goal: mkDiagramWithBoundary(b.build(), []), eliminations: [third, outer] }
}
