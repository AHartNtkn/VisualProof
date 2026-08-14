import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import { relSig, sigEquals } from '../../kernel/diagram/sig'
import { childCuts, headWireOf, nodesIn, propWires } from '../diagram-scan'
import type { PropFormula } from './formula'

export type PropTheoremReading = {
  readonly formula: PropFormula
  readonly wires: readonly WireId[]
}

/**
 * Read a closed propositional ∀-shell diagram back into a PropFormula:
 * root sheet holds exactly the shell's outer cut; the annulus holds the
 * proposition wires' pins; the inner cut is the body; inside, cuts are ¬,
 * juxtaposition is ∧, and atom heads are proposition occurrences. Pins are
 * presentational and skipped everywhere; anything else is a loud error.
 * Atom indices are positions in the id-sorted proposition wire list.
 */
export function readPropTheorem(diagram: Diagram): PropTheoremReading {
  const fail = (message: string): never => {
    throw new Error(`readPropTheorem: ${message}`)
  }
  const wires = propWires(diagram)
  if (wires.length !== Object.keys(diagram.wires).length) fail('diagram has non-proposition wires')
  const rootCuts = childCuts(diagram, diagram.root)
  if (nodesIn(diagram, diagram.root).length !== 0 || rootCuts.length !== 1) {
    fail('expected exactly the ∀ shell at the root')
  }
  const outer = rootCuts[0]!
  const outerCuts = childCuts(diagram, outer)
  if (outerCuts.length !== 1) fail('expected a single body cut inside the shell')
  for (const nodeId of nodesIn(diagram, outer)) {
    const node = diagram.nodes[nodeId]!
    if (!(node.kind === 'identity' && node.arity === 1)) fail(`annulus holds a non-pin node '${nodeId}'`)
  }
  const wireIndex = new Map(wires.map((id, index) => [id, index]))
  const readRegion = (region: RegionId): PropFormula => {
    const items: PropFormula[] = []
    for (const nodeId of nodesIn(diagram, region)) {
      const node = diagram.nodes[nodeId]!
      if (node.kind === 'identity' && node.arity === 1) continue
      if (node.kind !== 'atom') fail(`body holds unsupported node '${nodeId}' (${node.kind})`)
      if (!sigEquals(node.sig, relSig([]))) fail(`atom '${nodeId}' is not propositional`)
      const index = wireIndex.get(headWireOf(diagram, nodeId))
      if (index === undefined) fail(`atom '${nodeId}' heads an unknown wire`)
      items.push({ kind: 'atom', index: index! })
    }
    for (const cut of childCuts(diagram, region)) {
      items.push({ kind: 'not', body: readRegion(cut) })
    }
    if (items.length === 0) return { kind: 'top' }
    return items.reduce((left, right) => ({ kind: 'and', left, right }))
  }
  return { formula: readRegion(outerCuts[0]!), wires }
}
