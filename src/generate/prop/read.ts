import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import { relSig, sigEquals } from '../../kernel/diagram/sig'
import { childCuts, headWireOf, nodesIn, propWires } from '../diagram-scan'
import type { PropFormula } from './formula'

export type PropTheoremReading = {
  readonly formula: PropFormula
  readonly wires: readonly WireId[]
}

/**
 * Read one region of a propositional-fragment diagram into a PropFormula,
 * against a caller-supplied wire→index map: cuts are ¬, juxtaposition is
 * ∧, and atom heads are proposition occurrences keyed by their head wire's
 * index. Pins (arity-1 identity nodes) are presentational and skipped;
 * anything else is a loud error. Exported so callers that need to compare
 * two regions' content for exact structural sameness (walk normalization's
 * same-region duplicate finder) share this reader with `readPropTheorem`
 * rather than reimplementing it — comparing the resulting PropFormulas with
 * `sameFormula` (over a shared wire index) is sameness of content AND of
 * underlying wire identity, since the index is keyed by wire, not shape.
 */
export function readPropRegion(
  diagram: Diagram,
  region: RegionId,
  wireIndex: ReadonlyMap<WireId, number>,
): PropFormula {
  const fail = (message: string): never => {
    throw new Error(`readPropRegion: ${message}`)
  }
  const items: PropFormula[] = []
  for (const nodeId of nodesIn(diagram, region)) {
    const node = diagram.nodes[nodeId]!
    if (node.kind === 'identity' && node.arity === 1) continue
    if (node.kind !== 'atom') fail(`region holds unsupported node '${nodeId}' (${node.kind})`)
    if (!sigEquals(node.sig, relSig([]))) fail(`atom '${nodeId}' is not propositional`)
    const index = wireIndex.get(headWireOf(diagram, nodeId))
    if (index === undefined) fail(`atom '${nodeId}' heads an unindexed wire`)
    items.push({ kind: 'atom', index: index! })
  }
  for (const cut of childCuts(diagram, region)) {
    items.push({ kind: 'not', body: readPropRegion(diagram, cut, wireIndex) })
  }
  if (items.length === 0) return { kind: 'top' }
  return items.reduce((left, right) => ({ kind: 'and', left, right }))
}

/** The id-sorted proposition-wire index `readPropRegion` reads atoms
 *  against — the same indexing `readPropTheorem` uses for its output. */
export function propWireIndex(diagram: Diagram): ReadonlyMap<WireId, number> {
  return new Map(propWires(diagram).map((id, index) => [id, index]))
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
  const readRegion = (region: RegionId): PropFormula => {
    try {
      return readPropRegion(diagram, region, propWireIndex(diagram))
    } catch (error) {
      return fail(error instanceof Error ? error.message : String(error))
    }
  }
  return { formula: readRegion(outerCuts[0]!), wires }
}
