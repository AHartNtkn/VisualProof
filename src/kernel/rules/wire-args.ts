import type { DiagramWithBoundary } from '../diagram/boundary'
import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { derivedScope, isAncestorOrEqual, polarity, wireVisibleAt } from '../diagram/regions'
import type { RelSig, Sig } from '../diagram/sig'
import { relSig, sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { definitionSig } from './fold'
import {
  appliedEnds,
  attachArgs,
  completeWireEnds,
  deletePins,
  isPinEndpoint,
  pinEndpointsOf,
  relSigOf,
  requireRemovalScopePreserved,
  transferPins,
  wireAt,
  withoutEndpointsOf,
  type AppliedEnd,
  type PartsInProgress,
} from './wire-ends'

type Orientation = 'forward' | 'backward'

function requireGate(
  diagram: Diagram,
  scope: RegionId,
  orientation: Orientation,
  forwardNeed: 'positive' | 'negative',
  operation: string,
): void {
  const need = orientation === 'forward'
    ? forwardNeed
    : forwardNeed === 'positive' ? 'negative' : 'positive'
  const have = polarity(diagram, scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `${operation} requires a ${need} scope; '${scope}' is ${have}`,
    )
  }
}

function requirePosition(sig: RelSig, position: number, operation: string): void {
  if (!Number.isInteger(position) || position < 0 || position >= sig.args.length) {
    throw new RuleError(
      `${operation}: position ${position} is out of range for `
      + `'${sigKey(sig)}'`,
    )
  }
}

/**
 * Rebuild the acted-on wire with transformed ends. Every end's atom is
 * replaced by a fresh atom of `sig` whose argument tuple is produced by
 * `argsOf`; the old wire is replaced by one fresh wire carrying the heads.
 */
function replaceEnds(
  diagram: Diagram,
  wireId: WireId,
  ends: readonly AppliedEnd[],
  sig: RelSig,
  argsOf: (end: AppliedEnd) => readonly WireId[],
  freshSuffix: string,
  reservation?: IdReservation,
): Diagram {
  const old = wireAt(diagram, wireId)
  const oldScope = derivedScope(diagram, wireId)
  const pins = pinEndpointsOf(diagram, wireId)
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]

  const fresh = freshId(
    new Set(Object.keys(wires)),
    `${wireId}_${freshSuffix}`,
    reservation?.wires,
  )
  const endpoints: Endpoint[] = []
  const takenNodes = new Set(Object.keys(nodes))
  for (const end of ends) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: end.region, sig }
    endpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, argsOf(end))
  }
  void old
  wires[fresh] = { sig, endpoints }

  // Successor completion (spec §5): the acted wire's pins carry over, and
  // the successor is pinned at the old derived scope until it stands.
  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes, wires }
  transferPins(parts, pins, fresh)
  completeWireEnds(parts, fresh, oldScope, freshSuffix, reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/**
 * Equivalence: every end R(x̄) becomes R′(x̄, y) with y a fresh wire scoped
 * at that end's region — content with its own bound wire.
 */
export function applyArityShift(
  diagram: Diagram,
  wireId: WireId,
  newArgSig: Sig,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'arity shift')
  const sig = relSigOf(diagram, wireId, 'arity shift')
  const extended = relSig([...sig.args, newArgSig])

  const locals = new Map<NodeId, WireId>()
  const taken = new Set(Object.keys(diagram.wires))
  const takenNodes = new Set(Object.keys(diagram.nodes))
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  for (const end of ends) {
    const local = freshId(taken, `${wireId}_local`, reservation?.wires)
    taken.add(local)
    const pin = freshId(takenNodes, 'pin', reservation?.nodes)
    takenNodes.add(pin)
    nodes[pin] = { kind: 'identity', region: end.region, sig: newArgSig, arity: 1 }
    wires[local] = {
      sig: newArgSig,
      endpoints: [{ node: pin, port: { kind: 'identity', index: 0 } }],
    }
    locals.set(end.node, local)
  }

  return replaceEnds(
    { ...diagram, nodes, wires },
    wireId,
    ends,
    extended,
    (end) => [...end.args, locals.get(end.node)!],
    'shift',
    reservation,
  )
}

/**
 * Inverse of arity shift: the argument at `position` attaches, at every end,
 * to a wire scoped at that end's region whose only endpoint is that
 * attachment; the position and those wires drop.
 */
export function applyArityUnshift(
  diagram: Diagram,
  wireId: WireId,
  position: number,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'arity unshift')
  const sig = relSigOf(diagram, wireId, 'arity unshift')
  requirePosition(sig, position, 'arity unshift')

  const removedWires = new Set<WireId>()
  for (const end of ends) {
    const local = end.args[position]!
    const wire = wireAt(diagram, local)
    if (derivedScope(diagram, local) !== end.region) {
      throw new RuleError(
        `arity unshift requires the position-${position} wire of end `
        + `'${end.node}' to be scoped at the end's region; `
        + `'${local}' is scoped at '${derivedScope(diagram, local)}'`,
      )
    }
    const applied = wire.endpoints.filter((ep) => !isPinEndpoint(diagram, ep))
    if (applied.length !== 1) {
      throw new RuleError(
        `arity unshift requires the position-${position} wire of end `
        + `'${end.node}' to have that attachment as its only non-pin `
        + `endpoint; '${local}' has ${applied.length}`,
      )
    }
    removedWires.add(local)
  }

  const trimmed = relSig(sig.args.filter((_, index) => index !== position))
  const result = replaceEnds(
    diagram,
    wireId,
    ends,
    trimmed,
    (end) => end.args.filter((_, index) => index !== position),
    'unshift',
  )
  const wires: Record<WireId, Wire> = { ...result.wires }
  const nodes: Record<NodeId, DiagramNode> = { ...result.nodes }
  for (const local of removedWires) {
    for (const endpoint of wires[local]!.endpoints) {
      const node = nodes[endpoint.node]
      if (node !== undefined && node.kind === 'identity' && node.arity === 1) {
        delete nodes[endpoint.node]
      }
    }
    delete wires[local]
  }
  return mkDiagram({
    root: result.root,
    regions: { ...result.regions },
    nodes,
    wires,
  })
}

/** Equivalence: argument positions reorder by the given permutation. */
export function applyArgPermute(
  diagram: Diagram,
  wireId: WireId,
  permutation: readonly number[],
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'argument permute')
  const sig = relSigOf(diagram, wireId, 'argument permute')
  if (
    permutation.length !== sig.args.length
    || new Set(permutation).size !== sig.args.length
    || permutation.some((source) =>
      !Number.isInteger(source) || source < 0 || source >= sig.args.length)
  ) {
    throw new RuleError(
      `argument permute requires a permutation of ${sig.args.length} `
      + `position(s); got [${permutation.join(', ')}]`,
    )
  }

  const permuted = relSig(permutation.map((source) => sig.args[source]!))
  return replaceEnds(
    diagram,
    wireId,
    ends,
    permuted,
    (end) => permutation.map((source) => end.args[source]!),
    'permute',
    reservation,
  )
}

/** Equivalence: `position` gains a copy directly after it, on the same wire. */
export function applyArgDuplicate(
  diagram: Diagram,
  wireId: WireId,
  position: number,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'argument duplicate')
  const sig = relSigOf(diagram, wireId, 'argument duplicate')
  requirePosition(sig, position, 'argument duplicate')

  const args = [...sig.args]
  args.splice(position + 1, 0, sig.args[position]!)
  return replaceEnds(
    diagram,
    wireId,
    ends,
    relSig(args),
    (end) => {
      const tuple = [...end.args]
      tuple.splice(position + 1, 0, end.args[position]!)
      return tuple
    },
    'duplicate',
    reservation,
  )
}

/**
 * Inverse of duplicate: positions `position` and `position + 1` attach to the
 * same wire at every end; the copy drops.
 */
export function applyArgContract(
  diagram: Diagram,
  wireId: WireId,
  position: number,
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'argument contract')
  const sig = relSigOf(diagram, wireId, 'argument contract')
  requirePosition(sig, position, 'argument contract')
  requirePosition(sig, position + 1, 'argument contract')
  if (!sigEquals(sig.args[position]!, sig.args[position + 1]!)) {
    throw new RuleError(
      `argument contract requires equal signatures at positions `
      + `${position} and ${position + 1}`,
    )
  }
  for (const end of ends) {
    if (end.args[position] !== end.args[position + 1]) {
      throw new RuleError(
        `argument contract requires positions ${position} and ${position + 1} `
        + `to attach to the same wire at every end; end '${end.node}' has `
        + `'${end.args[position]}' and '${end.args[position + 1]}'`,
      )
    }
  }

  return replaceEnds(
    diagram,
    wireId,
    ends,
    relSig(sig.args.filter((_, index) => index !== position + 1)),
    (end) => end.args.filter((_, index) => index !== position + 1),
    'contract',
    reservation,
  )
}

/**
 * One shared attachment wire visible at the acted wire's scope makes the
 * dropped/extended position expressible at the binder (W := λx̄.W′(x̄, p)),
 * so both rewrite directions have witnesses and no polarity gate applies.
 * Per-site-varying attachments keep the directional gate.
 */
function uniformVisibleAttachment(
  diagram: Diagram,
  wireScope: RegionId,
  attachments: readonly WireId[],
): boolean {
  if (attachments.length === 0) return true
  const first = attachments[0]!
  if (attachments.some((wire) => wire !== first)) return false
  return wireVisibleAt(diagram, first, wireScope)
}

/** Gated (join family) unless the attachment is uniform and scope-visible. */
export function applyArgDrop(
  diagram: Diagram,
  wireId: WireId,
  position: number,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'dropping an argument')
  const sig = relSigOf(diagram, wireId, 'dropping an argument')
  requirePosition(sig, position, 'dropping an argument')
  if (!uniformVisibleAttachment(
    diagram,
    derivedScope(diagram, wireId),
    ends.map((end) => end.args[position]!),
  )) {
    requireGate(
      diagram,
      derivedScope(diagram, wireId),
      orientation,
      'negative',
      'dropping an argument',
    )
  }

  // Dropped-position wires lose one endpoint per end: class-(b) — their
  // quantifiers and floors must survive (wires still serving another
  // position keep replacement endpoints and are exempt).
  const keptElsewhere = new Set(
    ends.flatMap((end) => end.args.filter((_, index) => index !== position)),
  )
  requireRemovalScopePreserved(
    diagram,
    new Set(ends.map((end) => end.node)),
    new Set([wireId]),
    'dropping an argument',
    new Set(
      ends.map((end) => end.args[position]!).filter((w) => !keptElsewhere.has(w)),
    ),
  )
  return replaceEnds(
    diagram,
    wireId,
    ends,
    relSig(sig.args.filter((_, index) => index !== position)),
    (end) => end.args.filter((_, index) => index !== position),
    'drop',
    reservation,
  )
}

/**
 * Gated (sever family): a position appears at `position`, attached per end to
 * a chosen visible wire — the map is keyed by end node and must cover every
 * end exactly.
 */
export function applyArgExtend(
  diagram: Diagram,
  wireId: WireId,
  position: number,
  newArgSig: Sig,
  attachments: ReadonlyMap<NodeId, WireId>,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'extending an argument')
  const sig = relSigOf(diagram, wireId, 'extending an argument')
  if (
    !Number.isInteger(position) || position < 0 || position > sig.args.length
  ) {
    throw new RuleError(
      `extending an argument: position ${position} is out of range for `
      + `'${sigKey(sig)}'`,
    )
  }
  if (!uniformVisibleAttachment(
    diagram,
    derivedScope(diagram, wireId),
    ends.map((end) => attachments.get(end.node)).filter(
      (wire): wire is WireId => wire !== undefined,
    ),
  )) {
    requireGate(
      diagram,
      derivedScope(diagram, wireId),
      orientation,
      'positive',
      'extending an argument',
    )
  }
  if (
    attachments.size !== ends.length
    || ends.some((end) => !attachments.has(end.node))
  ) {
    throw new RuleError(
      `extending an argument requires an attachment covering every end of `
      + `'${wireId}' exactly once`,
    )
  }
  for (const end of ends) {
    const target = attachments.get(end.node)!
    const wire = wireAt(diagram, target)
    if (!sigEquals(wire.sig, newArgSig)) {
      throw new RuleError(
        `extending an argument expects '${sigKey(newArgSig)}'; `
        + `'${target}' has '${sigKey(wire.sig)}'`,
      )
    }
    if (!wireVisibleAt(diagram, target, end.region)) {
      throw new RuleError(
        `attachment wire '${target}' scoped at '${derivedScope(diagram, target)}' is not `
        + `visible at end '${end.node}' in region '${end.region}'`,
      )
    }
  }

  const args = [...sig.args]
  args.splice(position, 0, newArgSig)
  return replaceEnds(
    diagram,
    wireId,
    ends,
    relSig(args),
    (end) => {
      const tuple = [...end.args]
      tuple.splice(position, 0, attachments.get(end.node)!)
      return tuple
    },
    'extend',
    reservation,
  )
}

/**
 * Gated (join family): every end applies its own `position` argument to the
 * remaining arguments — the target wire differs per end, so no merge can
 * express this.
 */
export function applyApplyFormal(
  diagram: Diagram,
  wireId: WireId,
  position: number,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'applying a formal')
  const sig = relSigOf(diagram, wireId, 'applying a formal')
  requirePosition(sig, position, 'applying a formal')
  const rest = sig.args.filter((_, index) => index !== position)
  const head = sig.args[position]!
  if (head.kind !== 'rel' || !sigEquals(head, relSig(rest))) {
    throw new RuleError(
      `applying a formal: the signature at position ${position} `
      + `('${sigKey(head)}') must equal the relation signature of the `
      + `remaining arguments ('${sigKey(relSig(rest))}')`,
    )
  }
  requireGate(
    diagram,
    derivedScope(diagram, wireId),
    orientation,
    'negative',
    'applying a formal',
  )

  const pins = pinEndpointsOf(diagram, wireId)
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]
  deletePins(nodes, pins)

  const takenNodes = new Set(Object.keys(nodes))
  for (const end of ends) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: end.region, sig: head }
    const target = end.args[position]!
    const wire = wires[target]!
    wires[target] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, { node, port: { kind: 'head' } }],
    }
    attachArgs(wires, node, end.args.filter((_, index) => index !== position))
  }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}

/**
 * Inverse of apply-formal: atoms of one shared signature (their heads may
 * ride different wires) become applications of one fresh wire with the old
 * head as first argument.
 */
export function applyAbstractFormal(
  diagram: Diagram,
  ends: readonly NodeId[],
  scope: RegionId,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  if (ends.length === 0) {
    throw new RuleError('abstracting a formal requires at least one end')
  }
  if (diagram.regions[scope] === undefined) {
    throw new DiagramError(`unknown region '${scope}'`)
  }
  requireGate(diagram, scope, orientation, 'positive', 'abstracting a formal')

  type FormalEnd = {
    readonly node: NodeId
    readonly region: RegionId
    readonly head: WireId
    readonly args: readonly WireId[]
  }
  const resolved: FormalEnd[] = ends.map((nodeId) => {
    const node = diagram.nodes[nodeId]
    if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
    if (node.kind !== 'atom') {
      throw new RuleError(
        `abstracting a formal requires atom ends; '${nodeId}' is a ${node.kind}`,
      )
    }
    let head: WireId | undefined
    for (const [wireId, wire] of Object.entries(diagram.wires)) {
      if (wire.endpoints.some((endpoint) =>
        endpoint.node === nodeId && endpoint.port.kind === 'head')) {
        head = wireId
      }
    }
    if (head === undefined) {
      throw new DiagramError(`atom '${nodeId}' has no attached head wire`)
    }
    return {
      node: nodeId,
      region: node.region,
      head,
      args: node.sig.args.map((_, index) => {
        for (const [wireId, wire] of Object.entries(diagram.wires)) {
          if (wire.endpoints.some((endpoint) =>
            endpoint.node === nodeId
            && endpoint.port.kind === 'arg'
            && endpoint.port.index === index)) return wireId
        }
        throw new DiagramError(
          `atom '${nodeId}' has no attached wire at argument ${index}`,
        )
      }),
    }
  })
  const sig = (diagram.nodes[resolved[0]!.node] as Extract<DiagramNode, { kind: 'atom' }>).sig
  for (const end of resolved) {
    const node = diagram.nodes[end.node] as Extract<DiagramNode, { kind: 'atom' }>
    if (!sigEquals(node.sig, sig)) {
      throw new RuleError(
        `abstracting a formal requires one shared signature; '${end.node}' `
        + `has '${sigKey(node.sig)}' but '${resolved[0]!.node}' has '${sigKey(sig)}'`,
      )
    }
    if (!isAncestorOrEqual(diagram, scope, end.region)) {
      throw new RuleError(
        `scope '${scope}' does not enclose end '${end.node}' in region `
        + `'${end.region}'`,
      )
    }
  }

  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(resolved.map((end) => end.node))
  for (const end of resolved) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)

  const freshSig = relSig([sig, ...sig.args])
  const fresh = freshId(
    new Set(Object.keys(wires)),
    'formal',
    reservation?.wires,
  )
  const endpoints: Endpoint[] = []
  const takenNodes = new Set(Object.keys(nodes))
  for (const end of resolved) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'atom', region: end.region, sig: freshSig }
    endpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, [end.head, ...end.args])
  }
  wires[fresh] = { sig: freshSig, endpoints }

  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes, wires }
  completeWireEnds(parts, fresh, scope, 'abstracting a formal', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/** Gated (join family): every end becomes an identity node over its arguments. */
export function applyIdentityLeaf(
  diagram: Diagram,
  wireId: WireId,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'identity leaf')
  const sig = relSigOf(diagram, wireId, 'identity leaf')
  if (sig.args.length < 2) {
    throw new RuleError(
      `identity leaf requires at least two argument positions; `
      + `'${wireId}' has ${sig.args.length}`,
    )
  }
  const argSig = sig.args[0]!
  if (sig.args.some((candidate) => !sigEquals(candidate, argSig))) {
    throw new RuleError(
      `identity leaf requires equal argument signatures on '${wireId}'; `
      + `got '${sigKey(sig)}'`,
    )
  }
  requireGate(
    diagram,
    derivedScope(diagram, wireId),
    orientation,
    'negative',
    'identity leaf',
  )

  const pins = pinEndpointsOf(diagram, wireId)
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]
  deletePins(nodes, pins)

  const takenNodes = new Set(Object.keys(nodes))
  for (const end of ends) {
    const node = freshId(takenNodes, 'identity', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = {
      kind: 'identity',
      region: end.region,
      sig: argSig,
      arity: sig.args.length,
    }
    end.args.forEach((argWire, index) => {
      const wire = wires[argWire]!
      wires[argWire] = {
        sig: wire.sig,
        endpoints: [
          ...wire.endpoints,
          { node, port: { kind: 'identity', index } },
        ],
      }
    })
  }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}

/**
 * Inverse of identity leaf: identity nodes of one signature and arity become
 * ends of one fresh wire at `scope`.
 */
export function applyIdentityAbstract(
  diagram: Diagram,
  nodes: readonly NodeId[],
  scope: RegionId,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  if (nodes.length === 0) {
    throw new RuleError('identity abstract requires at least one node')
  }
  if (diagram.regions[scope] === undefined) {
    throw new DiagramError(`unknown region '${scope}'`)
  }
  requireGate(diagram, scope, orientation, 'positive', 'identity abstract')

  type IdentityEnd = {
    readonly node: NodeId
    readonly region: RegionId
    readonly args: readonly WireId[]
  }
  const resolved: IdentityEnd[] = nodes.map((nodeId) => {
    const node = diagram.nodes[nodeId]
    if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
    if (node.kind !== 'identity') {
      throw new RuleError(
        `identity abstract requires identity nodes; '${nodeId}' is a ${node.kind}`,
      )
    }
    if (!isAncestorOrEqual(diagram, scope, node.region)) {
      throw new RuleError(
        `scope '${scope}' does not enclose identity '${nodeId}' in region `
        + `'${node.region}'`,
      )
    }
    const args: WireId[] = []
    for (let index = 0; index < node.arity; index += 1) {
      let found: WireId | undefined
      for (const [wireId, wire] of Object.entries(diagram.wires)) {
        if (wire.endpoints.some((endpoint) =>
          endpoint.node === nodeId
          && endpoint.port.kind === 'identity'
          && endpoint.port.index === index)) found = wireId
      }
      if (found === undefined) {
        throw new DiagramError(
          `identity '${nodeId}' has no attached wire at port ${index}`,
        )
      }
      args.push(found)
    }
    return { node: nodeId, region: node.region, args }
  })
  const first = diagram.nodes[resolved[0]!.node] as Extract<DiagramNode, { kind: 'identity' }>
  for (const end of resolved) {
    const node = diagram.nodes[end.node] as Extract<DiagramNode, { kind: 'identity' }>
    if (!sigEquals(node.sig, first.sig) || node.arity !== first.arity) {
      throw new RuleError(
        `identity abstract requires one shared signature and arity; `
        + `'${end.node}' differs from '${resolved[0]!.node}'`,
      )
    }
  }

  const nextNodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(resolved.map((end) => end.node))
  for (const end of resolved) delete nextNodes[end.node]
  withoutEndpointsOf(wires, removed)

  const freshSig = relSig(Array.from({ length: first.arity }, () => first.sig))
  const fresh = freshId(
    new Set(Object.keys(wires)),
    'leaf',
    reservation?.wires,
  )
  const endpoints: Endpoint[] = []
  const takenNodes = new Set(Object.keys(nextNodes))
  for (const end of resolved) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nextNodes[node] = { kind: 'atom', region: end.region, sig: freshSig }
    endpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, end.args)
  }
  wires[fresh] = { sig: freshSig, endpoints }

  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes: nextNodes, wires }
  completeWireEnds(parts, fresh, scope, 'identity abstract', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}

/**
 * Gated (join family): every end becomes a reference to the named stored
 * definition — instantiating the bound relation wire at that macro, the way
 * identity leaf instantiates it at identity. Definitions are macros and are
 * never expanded implicitly, so content drawn with a folded reference
 * compiles to a step that introduces the reference as drawn. (Unfolding the
 * macro body, compiling it, and folding back would reach the same diagram,
 * but expands what the drawing keeps folded.)
 */
export function applyRefLeaf(
  diagram: Diagram,
  wireId: WireId,
  defId: string,
  definitions: ReadonlyMap<string, DiagramWithBoundary>,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  const ends = appliedEnds(diagram, wireId, 'ref leaf')
  const sig = relSigOf(diagram, wireId, 'ref leaf')
  const definition = definitions.get(defId)
  if (definition === undefined) {
    throw new RuleError(`ref leaf: no relation named '${defId}'`)
  }
  const expected = definitionSig(definition)
  if (!sigEquals(sig, expected)) {
    throw new RuleError(
      `ref leaf: wire '${wireId}' signature '${sigKey(sig)}' does not match `
      + `definition '${defId}' signature '${sigKey(expected)}'`,
    )
  }
  requireGate(
    diagram,
    derivedScope(diagram, wireId),
    orientation,
    'negative',
    'ref leaf',
  )

  const pins = pinEndpointsOf(diagram, wireId)
  const nodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(ends.map((end) => end.node))
  for (const end of ends) delete nodes[end.node]
  withoutEndpointsOf(wires, removed)
  delete wires[wireId]
  deletePins(nodes, pins)

  const takenNodes = new Set(Object.keys(nodes))
  for (const end of ends) {
    const node = freshId(takenNodes, 'ref', reservation?.nodes)
    takenNodes.add(node)
    nodes[node] = { kind: 'ref', region: end.region, defId, sig }
    attachArgs(wires, node, end.args)
  }

  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires,
  })
}

/**
 * Inverse of ref leaf: references to one definition become ends of one fresh
 * wire at `scope`.
 */
export function applyRefAbstract(
  diagram: Diagram,
  nodes: readonly NodeId[],
  scope: RegionId,
  orientation: Orientation = 'forward',
  reservation?: IdReservation,
): Diagram {
  if (nodes.length === 0) {
    throw new RuleError('ref abstract requires at least one node')
  }
  if (diagram.regions[scope] === undefined) {
    throw new DiagramError(`unknown region '${scope}'`)
  }
  requireGate(diagram, scope, orientation, 'positive', 'ref abstract')

  type RefEnd = {
    readonly node: NodeId
    readonly region: RegionId
    readonly args: readonly WireId[]
  }
  const resolved: RefEnd[] = nodes.map((nodeId) => {
    const node = diagram.nodes[nodeId]
    if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
    if (node.kind !== 'ref') {
      throw new RuleError(
        `ref abstract requires reference nodes; '${nodeId}' is a ${node.kind}`,
      )
    }
    if (!isAncestorOrEqual(diagram, scope, node.region)) {
      throw new RuleError(
        `scope '${scope}' does not enclose ref '${nodeId}' in region `
        + `'${node.region}'`,
      )
    }
    return {
      node: nodeId,
      region: node.region,
      args: node.sig.args.map((_, index) => {
        for (const [wireId, wire] of Object.entries(diagram.wires)) {
          if (wire.endpoints.some((endpoint) =>
            endpoint.node === nodeId
            && endpoint.port.kind === 'arg'
            && endpoint.port.index === index)) return wireId
        }
        throw new DiagramError(
          `ref '${nodeId}' has no attached wire at argument ${index}`,
        )
      }),
    }
  })
  const first = diagram.nodes[resolved[0]!.node] as Extract<DiagramNode, { kind: 'ref' }>
  for (const end of resolved) {
    const node = diagram.nodes[end.node] as Extract<DiagramNode, { kind: 'ref' }>
    if (node.defId !== first.defId || !sigEquals(node.sig, first.sig)) {
      throw new RuleError(
        `ref abstract requires one shared definition; '${end.node}' differs `
        + `from '${resolved[0]!.node}'`,
      )
    }
  }

  const nextNodes: Record<NodeId, DiagramNode> = { ...diagram.nodes }
  const wires: Record<WireId, Wire> = { ...diagram.wires }
  const removed = new Set(resolved.map((end) => end.node))
  for (const end of resolved) delete nextNodes[end.node]
  withoutEndpointsOf(wires, removed)

  const fresh = freshId(
    new Set(Object.keys(wires)),
    'refwire',
    reservation?.wires,
  )
  const endpoints: Endpoint[] = []
  const takenNodes = new Set(Object.keys(nextNodes))
  for (const end of resolved) {
    const node = freshId(takenNodes, 'n', reservation?.nodes)
    takenNodes.add(node)
    nextNodes[node] = { kind: 'atom', region: end.region, sig: first.sig }
    endpoints.push({ node, port: { kind: 'head' } })
    attachArgs(wires, node, end.args)
  }
  wires[fresh] = { sig: first.sig, endpoints }

  const parts: PartsInProgress = { regions: { ...diagram.regions }, nodes: nextNodes, wires }
  completeWireEnds(parts, fresh, scope, 'ref abstract', reservation?.nodes)
  return mkDiagram({ root: diagram.root, ...parts })
}
