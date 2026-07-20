import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../../src/kernel/diagram/diagram'

export type ComprehensionFixture = {
  readonly diagram: Diagram
  readonly guard: RegionId
  readonly bubble: RegionId
  readonly parameter: WireId
}

export function comprehensionFixture(): ComprehensionFixture {
  const builder = new DiagramBuilder()
  const guard = builder.cut(builder.root)
  const bubble = builder.bubble(guard, 2)
  for (let copy = 0; copy < 2; copy++) {
    const atom = builder.atom(bubble, bubble)
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 1 } }])
  }
  const context = builder.ref(builder.root, 'context', 1)
  const parameter = builder.wire(builder.root, [{ node: context, port: { kind: 'arg', index: 0 } }])
  return { diagram: builder.build(), guard, bubble, parameter }
}
