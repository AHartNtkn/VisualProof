import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import type { Diagram, RegionId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Closed-term introduction: mint a term node carrying a CLOSED term in any
 * region, riding a fresh singleton output wire scoped there.
 *
 * Soundness: every closed λ-term denotes an individual (its βη-class), so
 * ∃x(x = t) is valid for closed t. Adding a valid, self-contained conjunct
 * to ANY region is sound — in a positive region it is an equivalence
 * (φ ⟺ φ ∧ ψ when ⊨ ψ); therefore no polarity gate is required.
 * Hence no polarity gate. The K-trick (convert a host node's term u to
 * `(λv. u) t`, fission at ['arg'], convert back) already derives exactly
 * this whenever a host node exists in the region; the rule removes the host
 * requirement and replaces the three-step hack with one honest rule.
 *
 * Open terms must NOT be introducible this way: an open term's value depends
 * on its argument lines, and while ∃x(x = t(ā)) is still valid, the
 * attachment plumbing belongs to atomic open spawning and iteration. The
 * closed case is the one with zero entanglement.
 */
export function applyClosedTermIntro(d: Diagram, region: RegionId, term: Term): Diagram {
  if (d.regions[region] === undefined) throw new DiagramError(`unknown region '${region}'`)
  const free = freePorts(term)
  if (free.length > 0) {
    throw new RuleError(
      `closed-term introduction requires a closed term; free ports [${free.map((n) => `'${n}'`).join(', ')}] remain`,
    )
  }
  // Term well-formedness is mkDiagram's node check; rely on it.
  const nodeId = freshId(new Set(Object.keys(d.nodes)), `${region}_intro`)
  const wireId = freshId(new Set(Object.keys(d.wires)), `${region}_intro`)
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes, [nodeId]: { kind: 'term', region, term } },
    wires: {
      ...d.wires,
      [wireId]: { scope: region, endpoints: [{ node: nodeId, port: { kind: 'output' } }] },
    },
  })
}
