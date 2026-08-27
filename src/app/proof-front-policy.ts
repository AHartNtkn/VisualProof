import type { Diagram } from '../kernel/diagram/diagram'
import type { ProofStep } from '../kernel/proof/step'
import type { Hit } from './hittest'
import type { KeySample } from './interact/viewport'

export function stepActionLabel(step: ProofStep): string {
  return step.rule === 'theorem' ? `cite ${step.name}` : step.rule
}

export function frontKeyRoute(
  focused: boolean,
  sample: KeySample,
): KeySample | null {
  return focused ? sample : null
}

export function frontInputAllowed(
  focused: boolean,
  workspaceAllowed: boolean,
): boolean {
  return focused && workspaceAllowed
}

export function retainedFrontIds(
  diagram: Diagram,
  selection: readonly Hit[],
  pins: readonly string[],
): { readonly selection: readonly Hit[]; readonly pins: readonly string[] } {
  return {
    selection: selection.filter((hit) =>
      hit.kind === 'node'
        ? diagram.nodes[hit.id] !== undefined
        : hit.kind === 'region'
          ? diagram.regions[hit.id] !== undefined
          : diagram.wires[hit.id] !== undefined),
    pins: pins.filter((id) => diagram.nodes[id] !== undefined),
  }
}
