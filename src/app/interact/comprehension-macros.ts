import type { Diagram, NodeId, RegionId, WireId } from '../../kernel/diagram/diagram'
import { DiagramError } from '../../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../../kernel/diagram/boundary'
import type { RelSig, Sig } from '../../kernel/diagram/sig'
import { relSig } from '../../kernel/diagram/sig'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { IdReservation } from '../../kernel/diagram/subgraph/freshId'
import { applyBodyAttach, applyBodyDetach } from '../../kernel/rules/body'
import { applyUnfold, applyFold } from '../../kernel/rules/fold'
import { applyVacuousIntro, applyVacuousElim } from '../../kernel/rules/vacuous'

/**
 * Comprehension instantiation and abstraction as macros over the primitive
 * kernel rules. The old monolithic `applyComprehensionInstantiate` /
 * `applyComprehensionAbstract` (retired with the bubble model) are exactly the
 * composites below over signature-indexed wires — a relational wire IS the
 * existential relation variable `∃R`, a body node on it IS a witness `R := G`,
 * an atom whose head rides it IS an occurrence `R(⃗t)`.
 *
 * ORIENTATION PAIRING (derived from the primitive gates, not chosen freely).
 * A relational wire at a negative scope carries the forward-instantiation
 * direction; at a positive scope the backward one. Each primitive rule gates on
 * the polarity of the scope it touches, so within one macro the sub-rules that
 * touch the SAME scope must take opposite orientations:
 *
 *   • body attach forward ⇒ negative scope; backward ⇒ positive scope.
 *   • body detach forward ⇒ positive scope; backward ⇒ negative scope.
 *
 * Instantiate touches a wire at its own scope. Forward instantiate is a NEGATIVE
 * wire: attach uses the macro orientation (forward ⇒ negative, refuses a
 * positive wire exactly as the old rule refused a positive bubble); the trailing
 * detach removes the witness at that SAME negative scope, so it takes the
 * opposite orientation. Hence `attach = orientation`, `detach = flip(orientation)`.
 *
 * Abstract is the involution of instantiate: forward abstract is a POSITIVE
 * region. Attach must land the witness at that positive scope, so it takes the
 * FLIPPED orientation (backward ⇒ positive, refuses a negative region exactly as
 * the old rule refused a negative wrap); the trailing detach, at the same
 * positive scope, takes the macro orientation. Hence `attach = flip(orientation)`,
 * `detach = orientation`.
 */

type Orientation = 'forward' | 'backward'

const flip = (o: Orientation): Orientation => (o === 'forward' ? 'backward' : 'forward')

/** Unfold never consults a resolver for an atom flavor: the body node supplies the content. */
const noResolve = (_defId: string): DiagramWithBoundary | undefined => undefined

/** The id of the body node whose output endpoint rides `wireId`, or undefined for a bare wire. */
function bodyIdOnWire(d: Diagram, wireId: WireId): NodeId | undefined {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  for (const ep of w.endpoints) {
    if (ep.port.kind === 'output' && d.nodes[ep.node]?.kind === 'body') return ep.node
  }
  return undefined
}

/** The atom node ids whose head endpoint rides `wireId` (the body output is not an atom). */
function atomsOnWire(d: Diagram, wireId: WireId): NodeId[] {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  const out: NodeId[] = []
  for (const ep of w.endpoints) {
    if (ep.port.kind === 'head' && d.nodes[ep.node]?.kind === 'atom') out.push(ep.node)
  }
  return out
}

/**
 * The relation signature carried by a comprehension's ARGUMENT boundary — the
 * leading `comp.boundary.length - paramCount` wires' actual sigs. The trailing
 * `paramCount` wires are parameters (host lines the relation draws on) and are
 * NOT part of the relation's arity, so they are excluded here.
 */
function argBoundarySig(comp: DiagramWithBoundary, paramCount: number): RelSig {
  const argCount = comp.boundary.length - paramCount
  if (argCount < 0) {
    throw new DiagramError(
      `comprehension has ${comp.boundary.length} boundary wires but ${paramCount} parameters were given`,
    )
  }
  const args: Sig[] = comp.boundary.slice(0, argCount).map((wid) => {
    const w = comp.diagram.wires[wid]
    if (w === undefined) throw new DiagramError(`comprehension boundary wire '${wid}' is missing from the comprehension`)
    return w.sig
  })
  return relSig(args)
}

/**
 * Comprehension instantiation: `∃R. φ(R)` ⟶ `φ(G)`. Attach the witness `G` to
 * the relational wire, unfold every occurrence `R(⃗t)` that rides it into an
 * inlined copy of `G`, then detach the now-unreferenced witness and drop the
 * emptied wire. The final detach+vacuousElim is the wire-model image of the old
 * rule's bubble dissolution.
 *
 * `params` are the host lines feeding `G`'s parameter ports (shared across all
 * occurrences — that is what makes them parameters). Every gate of the composite
 * is a primitive gate: attach refuses a wire of the wrong polarity or a captured
 * parameter, its boundary arithmetic refuses an arity/attachment mismatch.
 */
export function macroComprehensionInstantiate(
  d: Diagram,
  wireId: WireId,
  comp: DiagramWithBoundary,
  params: readonly WireId[],
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const attached = applyBodyAttach(d, wireId, comp, params, orientation, reservation)
  // Collect occurrences up front: unfolding one atom never renames another.
  const atoms = atomsOnWire(attached, wireId)
  let cur = attached
  for (const atomId of atoms) {
    cur = applyUnfold(cur, atomId, noResolve, reservation)
  }
  const bodyId = bodyIdOnWire(cur, wireId)
  if (bodyId === undefined) throw new DiagramError(`instantiation lost the witness body on wire '${wireId}'`)
  cur = applyBodyDetach(cur, bodyId, flip(orientation))
  return applyVacuousElim(cur, wireId)
}

/** One occurrence of `G` to replace by an atom: its selection and the host wire per argument position. */
export type AbstractionOccurrence = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

/**
 * Comprehension abstraction: `φ(G)` ⟶ `∃R. φ(R)`, the involution of
 * instantiation. Introduce the fresh relational wire `∃R` at `wrapScope`, attach
 * the witness `G`, fold every chosen occurrence of `G` into an atom riding the
 * wire, then detach the witness to reach the pure `∃R. φ(R)` form the old rule
 * produced. No vacuousElim: the wire survives, carrying the folded occurrences.
 *
 * `params` are the host lines feeding `G`'s parameter ports — position-matched
 * to the comprehension's trailing boundary wires, exactly as in instantiation.
 * They are shared across every abstracted occurrence and are NOT arguments of
 * the relation: the wire's arity is derived from the LEADING boundary wires
 * only, so a parameterized comprehension abstracts to a parameterized relation
 * (the outer-bound-dependency feature) rather than a silently higher-arity one.
 * Each fold is exact: an occurrence whose boundary-pinned canonical form
 * (reordered by `args` over the arg positions, its parameter attachments landing
 * on `params`, diagonalized where `args` repeat) differs from `G` is refused by
 * the fold primitive.
 */
export function macroComprehensionAbstract(
  d: Diagram,
  wrapScope: RegionId,
  comp: DiagramWithBoundary,
  occurrences: readonly AbstractionOccurrence[],
  params: readonly WireId[] = [],
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const sig = argBoundarySig(comp, params.length)
  const before = new Set(Object.keys(d.wires))
  const introduced = applyVacuousIntro(d, wrapScope, sig, reservation)
  const wireId = Object.keys(introduced.wires).find((id) => !before.has(id))
  if (wireId === undefined) throw new DiagramError('vacuous introduction minted no wire')

  let cur = applyBodyAttach(introduced, wireId, comp, params, flip(orientation), reservation)
  for (const occ of occurrences) {
    cur = applyFold(cur, occ.sel, occ.args, { wireId }, reservation)
  }
  const bodyId = bodyIdOnWire(cur, wireId)
  if (bodyId === undefined) throw new DiagramError(`abstraction lost the witness body on wire '${wireId}'`)
  return applyBodyDetach(cur, bodyId, orientation)
}
