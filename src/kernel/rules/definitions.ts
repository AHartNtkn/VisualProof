import type { Term } from '../term/term'
import { cnst, freePorts, termEq, assertWellFormedTerm } from '../term/term'
import { printTerm } from '../term/print'
import type { PathSeg } from '../term/reduce'
import { subtermAt, replaceSubtermAt } from '../term/path'
import type { Diagram, DiagramNode, NodeId, RegionId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { RuleError } from './error'
import { termNodeAt } from './access'

/**
 * Definition environment for rule 7. Every body must stand alone: bvar-closed
 * (well-formed at depth 0, so substitution under binders needs no shifting)
 * and port-free (a definition cannot capture wiring). Plan 8's theory store
 * owns the environment; the rules just consume it.
 */
export type Definitions = Readonly<Record<string, Term>>

export function assertWellFormedDefinitions(defs: Definitions): void {
  for (const [id, body] of Object.entries(defs)) {
    if (id.length === 0) throw new DiagramError('definition id must be non-empty')
    try {
      assertWellFormedTerm(body)
    } catch (e) {
      throw new DiagramError(`definition '${id}': ${e instanceof Error ? e.message : String(e)}`)
    }
    const ports = freePorts(body)
    if (ports.length > 0) {
      throw new DiagramError(`definition '${id}' has free ports [${ports.join(', ')}]; definitions must be closed`)
    }
  }
}

function swapTerm(d: Diagram, nodeId: NodeId, region: RegionId, term: Term): Diagram {
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [nodeId]: { kind: 'term', region, term } }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires: { ...d.wires } })
}

/** Rule 7a (spec §3.1): replace a defined constant at a path by its body. Equivalence — no polarity gate. */
export function applyUnfold(d: Diagram, defs: Definitions, nodeId: NodeId, path: readonly PathSeg[]): Diagram {
  assertWellFormedDefinitions(defs)
  const node = termNodeAt(d, nodeId)
  let sub: Term
  try {
    sub = subtermAt(node.term, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (sub.kind !== 'const') {
    throw new RuleError(`unfold expects a constant at [${path.join(', ')}]; found '${sub.kind}'`)
  }
  const body = defs[sub.id]
  if (body === undefined) throw new RuleError(`no definition for constant '${sub.id}'`)
  return swapTerm(d, nodeId, node.region, replaceSubtermAt(node.term, path, body))
}

/** Rule 7b: replace a subterm syntactically equal to a definition body by the constant. */
export function applyFold(
  d: Diagram,
  defs: Definitions,
  nodeId: NodeId,
  path: readonly PathSeg[],
  constId: string,
): Diagram {
  assertWellFormedDefinitions(defs)
  const node = termNodeAt(d, nodeId)
  const body = defs[constId]
  if (body === undefined) throw new RuleError(`no definition for constant '${constId}'`)
  let sub: Term
  try {
    sub = subtermAt(node.term, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (!termEq(sub, body)) {
    throw new RuleError(
      `subterm '${printTerm(sub)}' at [${path.join(', ')}] is not syntactically the definition of '${constId}' ('${printTerm(body)}'); convert first (rule 5) if they are merely βη-equal`,
    )
  }
  return swapTerm(d, nodeId, node.region, replaceSubtermAt(node.term, path, cnst(constId)))
}
