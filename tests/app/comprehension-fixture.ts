import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../../src/kernel/diagram/diagram'

export type ComprehensionFixture = {
  readonly diagram: Diagram
  readonly guard: RegionId
  readonly bubble: RegionId
  readonly parameter: WireId
}

export type DependentComprehensionFixture = ComprehensionFixture & {
  readonly outerBinder: RegionId
  readonly hostAtom: NodeId
  readonly dependentBubble: RegionId
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

/** A production-surface fixture whose target is strictly enclosed by a
    nullary binder and has a separately pointer-reachable bound occurrence. */
export function dependentComprehensionFixture(): DependentComprehensionFixture {
  const builder = new DiagramBuilder()
  const guard = builder.cut(builder.root)
  const bubble = builder.bubble(guard, 2)
  for (let copy = 0; copy < 2; copy++) {
    const atom = builder.atom(bubble, bubble)
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 1 } }])
  }
  const outerBinder = builder.bubble(builder.root, 0)
  const hostAtom = builder.atom(outerBinder, outerBinder)
  const dependentBubble = builder.bubble(outerBinder, 0)
  builder.atom(dependentBubble, dependentBubble)
  const context = builder.ref(builder.root, 'context', 1)
  const parameter = builder.wire(builder.root, [{ node: context, port: { kind: 'arg', index: 0 } }])
  return {
    diagram: builder.build(), guard, outerBinder, hostAtom, bubble, dependentBubble, parameter,
  }
}
