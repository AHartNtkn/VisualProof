import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type {
  Diagram,
  DiagramNode,
  Endpoint,
  NodeId,
  Region,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { exploreForm, exploreIso } from '../diagram/canonical/explore'
import { mkDiagram } from '../diagram/diagram'
import { deepestCommonAncestor, derivedScope, derivedScopes, isAncestorOrEqual } from '../diagram/regions'
import type { RelSig, Sig } from '../diagram/sig'
import { relSig, sigEquals, sigKey } from '../diagram/sig'
import { extractSubgraph } from '../diagram/subgraph/extract'
import {
  selectionContents,
  type SelectionContents,
  type SubgraphSelection,
} from '../diagram/subgraph/selection'
import { removeSubgraph } from '../diagram/subgraph/splice'
import { freshId } from '../diagram/subgraph/freshId'
import { polarity } from '../diagram/regions'
import { RuleError } from '../rules/error'
import { bareWireDescription } from '../rules/identity-rules'
import { completeWireEnds } from '../rules/wire-ends'
import { mapStepIds } from './compose'
import type { ProofContext } from './context'
import type { ProofAction } from './action'
import {
  applyStepWithReceipt,
  type ProofStep,
} from './step'
import {
  extendIdReservation,
  type IdReservation,
} from '../diagram/subgraph/freshId'

/**
 * The authoring-layer compiler: fold a monolithic relation-grounding input
 * into the primitive step sequence realizing it, by structural induction on
 * the content diagram. The kernel never sees this module — the caller
 * replays the returned steps like any others.
 */

type Orientation = 'forward' | 'backward'

/** One live wire still owing content, plus its bookkeeping. */
type Residual = {
  /** Current host id of the live wire; its arity always equals `formals`. */
  readonly wire: WireId
  /**
   * The owed content. `boundary[0..formals)` are the wire's argument
   * positions in order; the suffix is the not-yet-materialized ambient
   * stubs, each mapping to a host wire in `ambients`.
   */
  readonly content: DiagramWithBoundary
  readonly formals: number
  readonly ambients: ReadonlyMap<WireId, WireId>
}

type Emitter = {
  current: () => Diagram
  emit: (step: ProofStep) => Diagram
}

function contentWire(content: DiagramWithBoundary, wireId: WireId): Wire {
  const wire = content.diagram.wires[wireId]
  if (wire === undefined) {
    throw new RuleError(`content wire '${wireId}' does not exist`)
  }
  return wire
}

/** Wires scoped at the content root that are binders, not boundary stubs. */
function internalRootWires(content: DiagramWithBoundary): WireId[] {
  const stubs = new Set(content.boundary)
  return Object.keys(content.diagram.wires)
    .filter((wireId) =>
      !stubs.has(wireId)
      && derivedScope(content.diagram, wireId, content.boundary) === content.diagram.root)
    .sort()
}

function rootCuts(content: DiagramWithBoundary): RegionId[] {
  return Object.entries(content.diagram.regions)
    .filter(([, region]) =>
      region.kind === 'cut' && region.parent === content.diagram.root)
    .map(([regionId]) => regionId)
    .sort()
}

function rootNodes(content: DiagramWithBoundary): NodeId[] {
  // A pin riding a boundary stub is interface apparatus (the drawn form of
  // a detached formal), not a content item to instantiate.
  const stubs = new Set(content.boundary)
  const stubPins = new Set<NodeId>()
  for (const [wireId, wire] of Object.entries(content.diagram.wires)) {
    if (!stubs.has(wireId)) continue
    for (const endpoint of wire.endpoints) {
      const node = content.diagram.nodes[endpoint.node]
      if (node !== undefined && node.kind === 'identity' && node.arity === 1) {
        stubPins.add(endpoint.node)
      }
    }
  }
  return Object.entries(content.diagram.nodes)
    .filter(([nodeId, node]) =>
      node.region === content.diagram.root && !stubPins.has(nodeId))
    .map(([nodeId]) => nodeId)
    .sort()
}

function regionSubtree(diagram: Diagram, root: RegionId): Set<RegionId> {
  const children = new Map<RegionId, RegionId[]>()
  for (const [regionId, region] of Object.entries(diagram.regions)) {
    if (region.kind === 'cut') {
      children.set(region.parent, [
        ...(children.get(region.parent) ?? []),
        regionId,
      ])
    }
  }
  const subtree = new Set<RegionId>([root])
  const queue = [root]
  while (queue.length > 0) {
    const next = queue.pop()!
    for (const child of children.get(next) ?? []) {
      subtree.add(child)
      queue.push(child)
    }
  }
  return subtree
}

/**
 * Restrict the content to one root item (a node or a cut subtree) or to its
 * complement. Boundary stubs are kept on both sides; their endpoints follow
 * their nodes.
 */
function restrictContent(
  content: DiagramWithBoundary,
  item: { readonly kind: 'node'; readonly id: NodeId }
    | { readonly kind: 'cut'; readonly id: RegionId },
  keep: 'item' | 'complement',
): DiagramWithBoundary {
  const diagram = content.diagram
  const stubs = new Set(content.boundary)
  const itemRegions = item.kind === 'cut'
    ? regionSubtree(diagram, item.id)
    : new Set<RegionId>()
  const keepNode = (nodeId: NodeId, node: DiagramNode): boolean => {
    const inItem = item.kind === 'node'
      ? nodeId === item.id
      : itemRegions.has(node.region)
    return keep === 'item' ? inItem : !inItem
  }
  const keepRegion = (regionId: RegionId): boolean => {
    if (regionId === diagram.root) return true
    const inItem = itemRegions.has(regionId)
    return keep === 'item' ? inItem : !inItem
  }

  const regions: Record<RegionId, Region> = {}
  for (const [regionId, region] of Object.entries(diagram.regions)) {
    if (keepRegion(regionId)) regions[regionId] = region
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [nodeId, node] of Object.entries(diagram.nodes)) {
    if (keepNode(nodeId, node)) nodes[nodeId] = node
  }
  const scopes = derivedScopes(diagram, content.boundary)
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (stubs.has(wireId)) {
      wires[wireId] = {
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          nodes[endpoint.node] !== undefined),
      }
    } else if (
      regions[scopes.get(wireId)!] !== undefined
      && scopes.get(wireId) !== diagram.root
      && wire.endpoints.every((endpoint) => nodes[endpoint.node] !== undefined)
    ) {
      wires[wireId] = wire
    }
  }
  pinDeficientStubs(content.boundary, nodes, wires, diagram.root)
  return mkDiagramWithBoundary(
    {
      root: diagram.root,
      regions,
      nodes,
      wires,
    },
    content.boundary,
  )
}

/**
 * A formal detached on one side of a restriction keeps only its boundary
 * entry; its drawn form is the wire from the frame exit to a root pin, so
 * the pin is minted here (deterministically) to satisfy the two-end floor.
 */
function pinDeficientStubs(
  boundary: readonly WireId[],
  nodes: Record<NodeId, DiagramNode>,
  wires: Record<WireId, Wire>,
  root: RegionId,
): void {
  const entries = new Map<WireId, number>()
  for (const wireId of boundary) {
    entries.set(wireId, (entries.get(wireId) ?? 0) + 1)
  }
  const taken = new Set(Object.keys(nodes))
  for (const [wireId, count] of entries) {
    const wire = wires[wireId]
    if (wire === undefined) continue
    if (wire.endpoints.length + count >= 2) continue
    const pin = freshId(taken, 'stubpin')
    taken.add(pin)
    nodes[pin] = { kind: 'identity', region: root, sig: wire.sig, arity: 1 }
    wires[wireId] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, { node: pin, port: { kind: 'identity', index: 0 } }],
    }
  }
}

/** Re-root the content into its single root cut (for cut wrap). */
function rerootContent(content: DiagramWithBoundary, cut: RegionId): DiagramWithBoundary {
  const diagram = content.diagram
  const subtree = regionSubtree(diagram, cut)
  const regions: Record<RegionId, Region> = {}
  for (const [regionId, region] of Object.entries(diagram.regions)) {
    if (regionId === cut) regions[regionId] = { kind: 'sheet' }
    else if (subtree.has(regionId)) regions[regionId] = region
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [nodeId, node] of Object.entries(diagram.nodes)) {
    if (subtree.has(node.region)) nodes[nodeId] = node
  }
  const scopes = derivedScopes(diagram, content.boundary)
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (new Set(content.boundary).has(wireId)) {
      wires[wireId] = {
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          nodes[endpoint.node] !== undefined),
      }
    } else if (subtree.has(scopes.get(wireId)!)) {
      wires[wireId] = wire
    }
  }
  pinDeficientStubs(content.boundary, nodes, wires, cut)
  return mkDiagramWithBoundary(
    { root: cut, regions, nodes, wires },
    content.boundary,
  )
}

/** The single new wire of the expected signature a rewriting step created. */
function newWireOfSig(before: Diagram, after: Diagram, sig: Sig): WireId {
  const fresh = Object.keys(after.wires).filter((wireId) =>
    before.wires[wireId] === undefined
    && sigEquals(after.wires[wireId]!.sig, sig))
  if (fresh.length !== 1) {
    throw new RuleError(
      `expected exactly one fresh '${sigKey(sig)}' wire, found ${fresh.length}`,
    )
  }
  return fresh[0]!
}

function newWiresOfSig(before: Diagram, after: Diagram, sig: Sig): WireId[] {
  return Object.keys(after.wires)
    .filter((wireId) =>
      before.wires[wireId] === undefined
      && sigEquals(after.wires[wireId]!.sig, sig))
    .sort()
}

/** The content-side attachment tuple of one node, in port order. */
function nodeAttachments(
  content: DiagramWithBoundary,
  nodeId: NodeId,
): { readonly head: WireId | undefined; readonly args: readonly WireId[] } {
  const diagram = content.diagram
  const node = diagram.nodes[nodeId]!
  const byPort = new Map<string, WireId>()
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    for (const endpoint of wire.endpoints) {
      if (endpoint.node !== nodeId) continue
      const port = endpoint.port
      const key = port.kind === 'head' ? 'hd' : `${port.kind}:${port.index}`
      byPort.set(key, wireId)
    }
  }
  const arity = node.kind === 'identity' ? node.arity : node.sig.args.length
  const portKind = node.kind === 'identity' ? 'identity' : 'arg'
  const args = Array.from({ length: arity }, (_, index) => {
    const wire = byPort.get(`${portKind}:${index}`)
    if (wire === undefined) {
      throw new RuleError(
        `content node '${nodeId}' has no attachment at position ${index}`,
      )
    }
    return wire
  })
  return { head: byPort.get('hd'), args }
}

/** Endpoints of the live wire in the host, as end-node ids. */
function liveEnds(diagram: Diagram, wireId: WireId): NodeId[] {
  return diagram.wires[wireId]!.endpoints.map((endpoint) => endpoint.node)
}

/**
 * Plumb the live wire so its argument-position stubs equal `target` exactly
 * (materializing ambients, dropping unused positions, duplicating repeats,
 * permuting into order). Returns the live wire's current id and the updated
 * position-stub list.
 */
function plumb(
  emitter: Emitter,
  residual: Residual,
  target: readonly WireId[],
): WireId {
  let wire = residual.wire
  const positions = [...residual.content.boundary.slice(0, residual.formals)]
  const ambients = residual.ambients
  const needed = new Set(target)
  const stubSig = (stub: WireId): Sig => contentWire(residual.content, stub).sig

  for (const stub of [...needed].sort()) {
    if (positions.includes(stub)) continue
    const host = ambients.get(stub)
    if (host === undefined) {
      throw new RuleError(`content stub '${stub}' is neither a position nor an ambient`)
    }
    const before = emitter.current()
    const attachments = Object.fromEntries(
      liveEnds(before, wire).map((end) => [end, host]),
    )
    const after = emitter.emit({
      rule: 'argExtend',
      wire,
      position: positions.length,
      newArgSig: stubSig(stub),
      attachments,
    })
    wire = newWireOfSig(before, after, relSig([...positions.map(stubSig), stubSig(stub)]))
    positions.push(stub)
  }

  for (let index = positions.length - 1; index >= 0; index -= 1) {
    if (needed.has(positions[index]!)) continue
    const before = emitter.current()
    const after = emitter.emit({ rule: 'argDrop', wire, position: index })
    positions.splice(index, 1)
    wire = newWireOfSig(before, after, relSig(positions.map(stubSig)))
  }

  for (let index = 0; index < target.length; index += 1) {
    if (positions[index] === target[index]) continue
    const later = positions.indexOf(target[index]!, index)
    if (later >= 0) {
      const permutation = positions.map((_, position) => position)
      permutation.splice(later, 1)
      permutation.splice(index, 0, later)
      const before = emitter.current()
      const after = emitter.emit({ rule: 'argPermute', wire, permutation })
      const moved = positions.splice(later, 1)[0]!
      positions.splice(index, 0, moved)
      wire = newWireOfSig(before, after, relSig(positions.map(stubSig)))
    } else {
      const earlier = positions.indexOf(target[index]!)
      if (earlier < 0 || earlier >= index) {
        throw new RuleError(
          `cannot arrange position ${index} for stub '${target[index]}'`,
        )
      }
      let before = emitter.current()
      let after = emitter.emit({ rule: 'argDuplicate', wire, position: earlier })
      positions.splice(earlier + 1, 0, positions[earlier]!)
      wire = newWireOfSig(before, after, relSig(positions.map(stubSig)))
      if (earlier + 1 !== index) {
        const permutation = positions.map((_, position) => position)
        permutation.splice(earlier + 1, 1)
        permutation.splice(index, 0, earlier + 1)
        before = emitter.current()
        after = emitter.emit({ rule: 'argPermute', wire, permutation })
        const moved = positions.splice(earlier + 1, 1)[0]!
        positions.splice(index, 0, moved)
        wire = newWireOfSig(before, after, relSig(positions.map(stubSig)))
      }
    }
  }
  if (
    positions.length !== target.length
    || positions.some((stub, index) => stub !== target[index])
  ) {
    throw new RuleError('argument plumbing failed to reach the target tuple')
  }
  return wire
}


/** Vacuity deletion of a bare (all-pin) wire, described from the diagram. */
function bareWireDeletion(diagram: Diagram, wireId: WireId): ProofStep {
  return {
    rule: 'vacuity',
    direction: 'delete',
    assembly: bareWireDescription(diagram, wireId),
  }
}

/**
 * The real ids a vacuity insertion minted, recovered by diffing: the delete
 * direction must name the apparatus as it exists.
 */
function mintedAssembly(
  pre: Diagram,
  post: Diagram,
  assembly: Extract<ProofStep, { rule: 'vacuity' }>['assembly'],
): Extract<ProofStep, { rule: 'vacuity' }>['assembly'] {
  const newNodeIds = Object.keys(post.nodes).filter((id) => pre.nodes[id] === undefined)
  const newWireIds = Object.keys(post.wires).filter((id) => pre.wires[id] === undefined)
  const nodes: Record<NodeId, { region: RegionId; sig: Sig; arity: number }> = {}
  for (const id of newNodeIds) {
    const node = post.nodes[id]!
    if (node.kind !== 'identity') {
      throw new RuleError(`vacuity inversion: minted node '${id}' is not an identity`)
    }
    nodes[id] = { region: node.region, sig: node.sig, arity: node.arity }
  }
  const wires: Record<WireId, { sig: Sig; endpoints: readonly Endpoint[] }> = {}
  for (const id of newWireIds) {
    const wire = post.wires[id]!
    wires[id] = { sig: wire.sig, endpoints: [...wire.endpoints] }
  }
  const attachments: Record<WireId, Endpoint[]> = {}
  for (const hostWireId of Object.keys(assembly.attachments)) {
    const before = new Set(pre.wires[hostWireId]!.endpoints.map((endpoint) =>
      `${endpoint.node}|${JSON.stringify(endpoint.port)}`))
    attachments[hostWireId] = post.wires[hostWireId]!.endpoints.filter((endpoint) =>
      !before.has(`${endpoint.node}|${JSON.stringify(endpoint.port)}`))
  }
  return { nodes, wires, attachments }
}

function endArgs(diagram: Diagram, nodeId: NodeId, arity: number): WireId[] {
  return     Array.from({ length: arity }, (_, index) => {
      for (const [wireId, wireValue] of Object.entries(diagram.wires)) {
        if (wireValue.endpoints.some((endpoint) =>
          endpoint.node === nodeId
          && endpoint.port.kind === 'arg'
          && endpoint.port.index === index)) return wireId
      }
      throw new RuleError(`invert: end '${nodeId}' lacks argument ${index}`)
    })
}

function handleLeaf(
  emitter: Emitter,
  residual: Residual,
  nodeId: NodeId,
): void {
  const node = residual.content.diagram.nodes[nodeId]!
  const attachments = nodeAttachments(residual.content, nodeId)
  const formalsSet = new Set(residual.content.boundary.slice(0, residual.formals))

  switch (node.kind) {
    case 'atom': {
      const head = attachments.head
      if (head === undefined) {
        throw new RuleError(`content atom '${nodeId}' has no head attachment`)
      }
      if (formalsSet.has(head) || residual.ambients.has(head)) {
        if (residual.ambients.has(head) && !formalsSet.has(head)) {
          const host = residual.ambients.get(head)!
          const wire = plumb(emitter, residual, attachments.args)
          emitter.emit({
            rule: 'wireJoin',
            input: { a: host, b: wire },
          })
        } else {
          const wire = plumb(emitter, residual, [head, ...attachments.args])
          emitter.emit({ rule: 'applyFormal', wire, position: 0 })
        }
        return
      }
      throw new RuleError(
        `content atom '${nodeId}' head '${head}' is neither a formal nor an ambient`,
      )
    }
    case 'ref': {
      const wire = plumb(emitter, residual, attachments.args)
      emitter.emit({ rule: 'refLeaf', wire, defId: node.defId })
      return
    }
    case 'identity': {
      if (node.arity >= 2) {
        const wire = plumb(emitter, residual, attachments.args)
        emitter.emit({ rule: 'identityLeaf', wire })
        return
      }
      // A point or a pin in the content is ⊤ apparatus: instantiate it at
      // every site by one vacuity insertion, then retire the live wire.
      const before = emitter.current()
      const ends = before.wires[residual.wire]!.endpoints
        .map((endpoint) => ({
          node: endpoint.node,
          region: before.nodes[endpoint.node]!.region,
        }))
        .filter(({ node: endNode }) => {
          const host = before.nodes[endNode]!
          return !(host.kind === 'identity' && host.arity === 1)
        })
      const assemblyNodes: Record<NodeId, { region: RegionId; sig: Sig; arity: number }> = {}
      const assemblyAttachments: Record<WireId, Endpoint[]> = {}
      ends.forEach((end, index) => {
        const label = `leafpt${index}`
        assemblyNodes[label] = { region: end.region, sig: node.sig, arity: node.arity }
        if (node.arity === 1) {
          const target = attachments.args[0]!
          const host = residual.ambients.get(target)
            ?? (() => {
              const position = residual.content.boundary
                .slice(0, residual.formals)
                .indexOf(target)
              if (position < 0) {
                throw new RuleError(
                  `content pin '${nodeId}' attaches to '${target}', which is `
                  + `neither a formal nor an ambient`,
                )
              }
              return endArgs(before, end.node, residual.formals)[position]!
            })()
          assemblyAttachments[host] = [
            ...(assemblyAttachments[host] ?? []),
            { node: label, port: { kind: 'identity', index: 0 } },
          ]
        }
      })
      emitter.emit({
        rule: 'vacuity',
        direction: 'insert',
        assembly: { nodes: assemblyNodes, wires: {}, attachments: assemblyAttachments },
      })
      emitter.emit({ rule: 'endsDelete', wire: residual.wire })
      emitter.emit(bareWireDeletion(emitter.current(), residual.wire))
      return
    }
  }
}

function handleResidual(emitter: Emitter, residual: Residual): Residual[] {
  const internal = internalRootWires(residual.content)
  if (internal.length > 0) {
    const binder = internal[0]!
    const binderSig = contentWire(residual.content, binder).sig
    const before = emitter.current()
    const after = emitter.emit({
      rule: 'arityShift',
      wire: residual.wire,
      newArgSig: binderSig,
    })
    const positionSigs = residual.content.boundary
      .slice(0, residual.formals)
      .map((stub) => contentWire(residual.content, stub).sig)
    const wire = newWireOfSig(before, after, relSig([...positionSigs, binderSig]))
    const boundary = [
      ...residual.content.boundary.slice(0, residual.formals),
      binder,
      ...residual.content.boundary.slice(residual.formals),
    ]
    return [{
      wire,
      content: mkDiagramWithBoundary(residual.content.diagram, boundary),
      formals: residual.formals + 1,
      ambients: residual.ambients,
    }]
  }

  const cuts = rootCuts(residual.content)
  const nodes = rootNodes(residual.content)
  const items = cuts.length + nodes.length

  if (items === 0) {
    emitter.emit({ rule: 'endsDelete', wire: residual.wire })
    emitter.emit(bareWireDeletion(emitter.current(), residual.wire))
    return []
  }

  if (items >= 2) {
    const item = nodes.length > 0
      ? { kind: 'node' as const, id: nodes[0]! }
      : { kind: 'cut' as const, id: cuts[0]! }
    const first = restrictContent(residual.content, item, 'item')
    const rest = restrictContent(residual.content, item, 'complement')
    const sig = emitter.current().wires[residual.wire]!.sig
    const before = emitter.current()
    const after = emitter.emit({ rule: 'parallelSplit', wire: residual.wire })
    const [left, right] = newWiresOfSig(before, after, sig)
    if (left === undefined || right === undefined) {
      throw new RuleError('parallel split did not produce two fresh wires')
    }
    return [
      { ...residual, wire: left, content: first },
      { ...residual, wire: right, content: rest },
    ]
  }

  if (cuts.length === 1) {
    const sig = emitter.current().wires[residual.wire]!.sig
    const before = emitter.current()
    const after = emitter.emit({ rule: 'cutWrap', wire: residual.wire })
    const wire = newWireOfSig(before, after, sig)
    return [{
      ...residual,
      wire,
      content: rerootContent(residual.content, cuts[0]!),
    }]
  }

  handleLeaf(emitter, residual, nodes[0]!)
  return []
}

/**
 * Compile a monolithic relation join — instantiate `wire` with `content`
 * over `parameters` — into primitive steps. The returned list, replayed in
 * order with the same orientation, produces the monolith's result.
 */
export type CompileOptions = {
  readonly reservation?: IdReservation
  readonly onStep?: (step: ProofStep, before: Diagram, after: Diagram) => void
}

export function compileRelationJoin(
  diagram: Diagram,
  wire: WireId,
  content: DiagramWithBoundary,
  parameters: readonly WireId[],
  context: ProofContext,
  orientation: Orientation = 'forward',
  options: CompileOptions = {},
): ProofStep[] {
  const relation = diagram.wires[wire]
  if (relation === undefined) {
    throw new RuleError(`unknown wire '${wire}'`)
  }
  if (relation.sig.kind !== 'rel') {
    throw new RuleError(
      `relation grounding requires a relation wire; '${wire}' has `
      + `'${sigKey(relation.sig)}'`,
    )
  }
  const validated = mkDiagramWithBoundary(content.diagram, content.boundary)
  const arity = relation.sig.args.length
  if (validated.boundary.length !== arity + parameters.length) {
    throw new RuleError(
      `content boundary has ${validated.boundary.length} positions; expected `
      + `${arity} formal(s) plus ${parameters.length} parameter(s)`,
    )
  }
  const ambients = new Map<WireId, WireId>()
  validated.boundary.slice(arity).forEach((stub, index) => {
    const host = parameters[index]!
    const hostWire = diagram.wires[host]
    if (hostWire === undefined) {
      throw new RuleError(`unknown parameter wire '${host}'`)
    }
    const hostScope = derivedScope(diagram, host)
    const relationScope = derivedScope(diagram, wire)
    if (!isAncestorOrEqual(diagram, hostScope, relationScope)) {
      throw new RuleError(
        `parameter '${host}' scope '${hostScope}' must enclose relation `
        + `scope '${relationScope}'`,
      )
    }
    ambients.set(stub, host)
  })

  const steps: ProofStep[] = []
  let current = diagram
  let reservation = options.reservation
  const apply = (step: ProofStep): Diagram => {
    const before = current
    const receipt = applyStepWithReceipt(
      current,
      step,
      context,
      orientation,
      reservation,
    )
    current = receipt.result
    reservation = extendIdReservation(reservation, receipt.allocation)
    steps.push(step)
    options.onStep?.(step, before, current)
    return current
  }
  // Completion pins are per-step scaffolding; a pin whose removal changes
  // neither a scope nor a floor holds nothing, and sweeping it keeps the
  // compiled shape pin-minimal (the shape the target diagrams state).
  const sweepScaffoldPins = (): void => {
    for (;;) {
      let swept = false
      for (const wireId of Object.keys(current.wires).sort()) {
        const wire = current.wires[wireId]!
        if (wire.endpoints.length <= 2) continue
        const scope = derivedScope(current, wireId)
        for (const endpoint of [...wire.endpoints].sort((a, b) =>
          a.node < b.node ? -1 : a.node > b.node ? 1 : 0)) {
          const node = current.nodes[endpoint.node]
          if (node === undefined || node.kind !== 'identity' || node.arity !== 1) continue
          const rest = wire.endpoints.filter((candidate) => candidate.node !== endpoint.node)
          if (rest.length < 2) continue
          let dca: RegionId | null = null
          for (const other of rest) {
            const region = current.nodes[other.node]!.region
            dca = dca === null ? region : deepestCommonAncestor(current, dca, region)
          }
          if (dca !== scope) continue
          apply({
            rule: 'vacuity',
            direction: 'delete',
            assembly: {
              nodes: { [endpoint.node]: { region: node.region, sig: node.sig, arity: 1 } },
              wires: {},
              attachments: { [wireId]: [endpoint] },
            },
          })
          swept = true
          break
        }
        if (swept) break
      }
      if (!swept) return
    }
  }
  const emitter: Emitter = {
    current: () => current,
    emit: (step) => {
      apply(step)
      sweepScaffoldPins()
      return current
    },
  }

  const worklist: Residual[] = [{
    wire,
    content: validated,
    formals: arity,
    ambients,
  }]
  while (worklist.length > 0) {
    const residual = worklist.pop()!
    worklist.push(...handleResidual(emitter, residual))
  }
  return steps
}

/** One explicitly designated exact occurrence to abstract. */
export type SeverOccurrence = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

/** Durable relation-abstraction input: scope plus designated occurrences. */
export type RelationSeverInput = {
  readonly scope: RegionId
  readonly occurrences: readonly SeverOccurrence[]
}

type PreparedOccurrenceContent = {
  readonly pattern: DiagramWithBoundary
  readonly ambientAttachments: readonly WireId[]
}

function prepareOccurrence(
  diagram: Diagram,
  occurrence: SeverOccurrence,
): PreparedOccurrenceContent {
  const extracted = extractSubgraph(diagram, occurrence.sel)
  const stubByAttachment = new Map<WireId, WireId>()
  extracted.attachments.forEach((attachment, index) => {
    stubByAttachment.set(attachment, extracted.pattern.boundary[index]!)
  })
  const formalBoundary = occurrence.args.map((attachment, index) => {
    if (diagram.wires[attachment] === undefined) {
      throw new RuleError(`unknown formal argument wire '${attachment}'`)
    }
    const stub = stubByAttachment.get(attachment)
    if (stub === undefined) {
      throw new RuleError(
        `formal argument ${index} wire '${attachment}' does not touch `
        + 'the selected content',
      )
    }
    return stub
  })
  const formalSet = new Set(occurrence.args)
  const ambientAttachments = extracted.attachments.filter(
    (attachment) => !formalSet.has(attachment),
  )
  return {
    pattern: mkDiagramWithBoundary(
      extracted.pattern.diagram,
      [
        ...formalBoundary,
        ...ambientAttachments.map((attachment) =>
          stubByAttachment.get(attachment)!),
      ],
    ),
    ambientAttachments,
  }
}

function intersects<T>(left: ReadonlySet<T>, right: ReadonlySet<T>): boolean {
  for (const item of left) {
    if (right.has(item)) return true
  }
  return false
}

function contentsEmpty(contents: SelectionContents): boolean {
  return contents.allRegions.size === 0
    && contents.allNodes.size === 0
    && contents.internalWires.length === 0
}

function assertDisjointOccurrences(
  occurrences: readonly {
    readonly occurrence: SeverOccurrence
    readonly contents: SelectionContents
  }[],
): void {
  for (let leftIndex = 0; leftIndex < occurrences.length; leftIndex++) {
    const left = occurrences[leftIndex]!
    for (
      let rightIndex = leftIndex + 1;
      rightIndex < occurrences.length;
      rightIndex++
    ) {
      const right = occurrences[rightIndex]!
      if (
        left.contents.allRegions.has(right.occurrence.sel.region)
        || right.contents.allRegions.has(left.occurrence.sel.region)
      ) {
        throw new RuleError(
          'an occurrence site is selected recursively inside another occurrence',
        )
      }
      if (
        left.occurrence.sel.region === right.occurrence.sel.region
        && contentsEmpty(left.contents)
        && contentsEmpty(right.contents)
      ) {
        throw new RuleError(
          `duplicate empty content at the same occurrence site `
          + `'${left.occurrence.sel.region}'`,
        )
      }
      if (
        intersects(left.contents.allRegions, right.contents.allRegions)
        || intersects(left.contents.allNodes, right.contents.allNodes)
        || intersects(
          new Set(left.contents.internalWires),
          new Set(right.contents.internalWires),
        )
      ) {
        throw new RuleError(
          `relation sever occurrences ${leftIndex} and ${rightIndex} overlap`,
        )
      }
    }
  }
}

/**
 * The abstraction result the compiled sequence must reach: occurrences
 * removed, one fresh relation wire applied at every site.
 */
function constructSevered(
  diagram: Diagram,
  input: RelationSeverInput,
  orientation: Orientation,
): {
  readonly severed: Diagram
  readonly wire: WireId
  readonly pattern: DiagramWithBoundary
  readonly ambientAttachments: readonly WireId[]
} {
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(diagram, input.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `relation wire sever requires a ${need} scope; `
      + `'${input.scope}' is ${have}`,
    )
  }
  if (input.occurrences.length === 0) {
    throw new RuleError('relation wire sever requires at least one occurrence')
  }
  const contents = input.occurrences.map((occurrence) => ({
    occurrence,
    contents: selectionContents(diagram, occurrence.sel),
  }))
  assertDisjointOccurrences(contents)
  for (const { occurrence } of contents) {
    if (!isAncestorOrEqual(diagram, input.scope, occurrence.sel.region)) {
      throw new RuleError(
        `occurrence region '${occurrence.sel.region}' must descend from `
        + `quantifier scope '${input.scope}'`,
      )
    }
  }
  const prepared = input.occurrences.map((occurrence) =>
    prepareOccurrence(diagram, occurrence))
  const first = prepared[0]!
  const firstFormalSigs = input.occurrences[0]!.args.map((attachment) =>
    diagram.wires[attachment]!.sig)
  const firstForm = exploreForm(first.pattern.diagram, first.pattern.boundary)
  for (const [index, candidate] of prepared.entries()) {
    if (index === 0) continue
    const args = input.occurrences[index]!.args
    if (args.length !== firstFormalSigs.length) {
      throw new RuleError(
        `occurrence ${index} has ${args.length} formal arguments; `
        + `expected ${firstFormalSigs.length}`,
      )
    }
    args.forEach((attachment, argumentIndex) => {
      const actual = diagram.wires[attachment]!.sig
      const expected = firstFormalSigs[argumentIndex]!
      if (!sigEquals(actual, expected)) {
        throw new RuleError(
          `formal argument ${argumentIndex} signature differs across `
          + `occurrences: '${sigKey(expected)}' vs '${sigKey(actual)}'`,
        )
      }
    })
    if (
      candidate.ambientAttachments.length !== first.ambientAttachments.length
      || candidate.ambientAttachments.some((attachment, position) =>
        attachment !== first.ambientAttachments[position])
    ) {
      throw new RuleError(
        'ambient attachments must be identical host wires in every occurrence',
      )
    }
    if (
      exploreForm(candidate.pattern.diagram, candidate.pattern.boundary)
      !== firstForm
    ) {
      throw new RuleError(
        'occurrences are not isomorphic under the same pinned content',
      )
    }
  }
  for (const attachment of first.ambientAttachments) {
    const parameterScope = derivedScope(diagram, attachment)
    if (!isAncestorOrEqual(diagram, parameterScope, input.scope)) {
      throw new RuleError(
        `ambient attachment '${attachment}' scope '${parameterScope}' `
        + `must enclose quantifier scope '${input.scope}'`,
      )
    }
  }

  let result = diagram
  for (const occurrence of input.occurrences) {
    result = removeSubgraph(result, occurrence.sel)
  }
  const quantifierSig = relSig(input.occurrences[0]!.args.map((attachment) =>
    diagram.wires[attachment]!.sig))
  const takenNodes = new Set(Object.keys(diagram.nodes))
  const quantifierId = freshId(
    new Set(Object.keys(diagram.wires)),
    'wire_quantifier',
  )
  const nodes: Record<NodeId, DiagramNode> = { ...result.nodes }
  const wires: Record<WireId, Wire> = { ...result.wires }
  const quantifierEndpoints: Endpoint[] = []
  input.occurrences.forEach((occurrence, occurrenceIndex) => {
    const nodeId = freshId(
      takenNodes,
      `wire_quantifier_atom_${occurrenceIndex}`,
    )
    takenNodes.add(nodeId)
    nodes[nodeId] = {
      kind: 'atom',
      region: occurrence.sel.region,
      sig: quantifierSig,
    }
    quantifierEndpoints.push({ node: nodeId, port: { kind: 'head' } })
    occurrence.args.forEach((attachment, argumentIndex) => {
      const existing = wires[attachment]
      if (existing === undefined) {
        throw new RuleError(
          `formal argument wire '${attachment}' did not survive content removal`,
        )
      }
      wires[attachment] = {
        sig: existing.sig,
        endpoints: [
          ...existing.endpoints,
          { node: nodeId, port: { kind: 'arg', index: argumentIndex } },
        ],
      }
    })
  })
  wires[quantifierId] = {
    sig: quantifierSig,
    endpoints: quantifierEndpoints,
  }
  const parts = { regions: { ...result.regions }, nodes, wires }
  completeWireEnds(parts, quantifierId, input.scope, 'relation wire sever')
  return {
    severed: mkDiagram({ root: result.root, ...parts }),
    wire: quantifierId,
    pattern: first.pattern,
    ambientAttachments: first.ambientAttachments,
  }
}

/**
 * Compile a relation sever into primitive steps: plan the inverse join
 * against the (virtually) severed diagram, then emit each planned step's
 * inverse in reverse order, transporting ids through per-step isomorphisms
 * into the caller's real diagram.
 */
export function compileRelationSever(
  diagram: Diagram,
  input: RelationSeverInput,
  context: ProofContext,
  orientation: Orientation = 'forward',
  options: CompileOptions = {},
): {
  readonly steps: ProofStep[]
  readonly diffs: readonly { readonly before: Diagram; readonly after: Diagram }[]
} {
  const {
    severed,
    wire,
    pattern,
    ambientAttachments,
  } = constructSevered(diagram, input, orientation)

  const trace: Array<{ step: ProofStep; pre: Diagram; post: Diagram }> = []
  const joinOrientation: Orientation =
    orientation === 'forward' ? 'backward' : 'forward'
  {
    compileRelationJoin(
      severed,
      wire,
      pattern,
      ambientAttachments,
      context,
      joinOrientation,
      {
        onStep: (step, before, after) => {
          trace.push({ step, pre: before, post: after })
        },
      },
    )
    const finalState = trace.length > 0 ? trace[trace.length - 1]!.post : severed
    const finalIso = exploreIso(finalState, diagram)
    if (finalIso === null) {
      throw new RuleError(
        'sever compilation failed: the planned join does not reproduce the diagram\n'
        + `-- planned:\n${exploreForm(finalState)}\n-- actual:\n${exploreForm(diagram)}`,
      )
    }
  }

  const output: ProofStep[] = []
  const diffs: Array<{ before: Diagram; after: Diagram }> = []
  let real = diagram
  let reservation = options.reservation
  for (let index = trace.length - 1; index >= 0; index -= 1) {
    const { step, pre, post } = trace[index]!
    const iso = exploreIso(post, real)
    if (iso === null) {
      throw new RuleError(
        `sever compilation lost the isomorphism before inverting step ${index} `
        + `(${step.rule})\n-- planned post:\n${exploreForm(post)}\n-- real:\n${exploreForm(real)}`,
      )
    }
    const inverse = invertStep(step, pre, post)
    const mapped = mapStepIds(inverse, iso)
    const before = real
    const receipt = applyStepWithReceipt(
      real,
      mapped,
      context,
      orientation,
      reservation,
    )
    real = receipt.result
    reservation = extendIdReservation(reservation, receipt.allocation)
    diffs.push({ before, after: real })
    output.push(mapped)
    options.onStep?.(mapped, before, real)
  }
  return { steps: output, diffs }
}

/** The planning-world inverse of one emitted join step. */
function invertStep(step: ProofStep, pre: Diagram, post: Diagram): ProofStep {
  const preWire = (wireId: WireId): Wire => {
    const wire = pre.wires[wireId]
    if (wire === undefined) {
      throw new RuleError(`invert: wire '${wireId}' missing before its step`)
    }
    return wire
  }
  // Completion pins minted alongside a step are scaffolding, not ends.
  const newNodes = (): NodeId[] =>
    Object.keys(post.nodes).filter((nodeId) => {
      if (pre.nodes[nodeId] !== undefined) return false
      const node = post.nodes[nodeId]!
      return !(node.kind === 'identity' && node.arity <= 1)
    })

  switch (step.rule) {
    case 'arityShift': {
      const old = preWire(step.wire)
      const oldSig = old.sig as RelSig
      const fresh = newWireOfSig(
        pre,
        post,
        relSig([...oldSig.args, step.newArgSig]),
      )
      return { rule: 'arityUnshift', wire: fresh, position: oldSig.args.length }
    }
    case 'parallelSplit': {
      const sig = preWire(step.wire).sig
      const [left, right] = newWiresOfSig(pre, post, sig)
      if (left === undefined || right === undefined) {
        throw new RuleError('invert: parallel split without two fresh wires')
      }
      return { rule: 'parallelFuse', a: left, b: right }
    }
    case 'cutWrap': {
      const fresh = newWireOfSig(pre, post, preWire(step.wire).sig)
      return { rule: 'cutAbsorb', wire: fresh }
    }
    case 'endsDelete': {
      const old = preWire(step.wire)
      const oldSig = old.sig as RelSig
      return {
        rule: 'endsSpawn',
        wire: step.wire,
        sites: old.endpoints
          .filter((endpoint) => {
            const node = pre.nodes[endpoint.node]!
            return !(node.kind === 'identity' && node.arity === 1)
          })
          .map((endpoint) => ({
            region: pre.nodes[endpoint.node]!.region,
            args: endArgs(pre, endpoint.node, oldSig.args.length),
          })),
      }
    }
    case 'vacuity': {
      if (step.direction === 'insert') {
        return { rule: 'vacuity', direction: 'delete', assembly: mintedAssembly(pre, post, step.assembly) }
      }
      return { rule: 'vacuity', direction: 'insert', assembly: step.assembly }
    }
    case 'argExtend': {
      const old = preWire(step.wire)
      const oldSig = old.sig as RelSig
      const args = [...oldSig.args]
      args.splice(step.position, 0, step.newArgSig)
      const fresh = newWireOfSig(pre, post, relSig(args))
      return { rule: 'argDrop', wire: fresh, position: step.position }
    }
    case 'argDrop': {
      const old = preWire(step.wire)
      const oldSig = old.sig as RelSig
      const args = oldSig.args.filter((_, index) => index !== step.position)
      const fresh = newWireOfSig(pre, post, relSig(args))
      const applied = (diagram: Diagram, endpoints: readonly Endpoint[]): NodeId[] =>
        endpoints
          .filter((endpoint) => {
            const node = diagram.nodes[endpoint.node]!
            return !(node.kind === 'identity' && node.arity === 1)
          })
          .map((endpoint) => endpoint.node)
      const preEnds = applied(pre, old.endpoints)
      const postEnds = applied(post, post.wires[fresh]!.endpoints)
      const attachments = Object.fromEntries(postEnds.map((node, index) => [
        node,
        endArgs(pre, preEnds[index]!, oldSig.args.length)[step.position]!,
      ]))
      return {
        rule: 'argExtend',
        wire: fresh,
        position: step.position,
        newArgSig: oldSig.args[step.position]!,
        attachments,
      }
    }
    case 'argPermute': {
      const old = preWire(step.wire)
      const oldSig = old.sig as RelSig
      const fresh = newWireOfSig(
        pre,
        post,
        relSig(step.permutation.map((source) => oldSig.args[source]!)),
      )
      const inverse = step.permutation.map((_, index) =>
        step.permutation.indexOf(index))
      return { rule: 'argPermute', wire: fresh, permutation: inverse }
    }
    case 'argDuplicate': {
      const old = preWire(step.wire)
      const oldSig = old.sig as RelSig
      const args = [...oldSig.args]
      args.splice(step.position + 1, 0, oldSig.args[step.position]!)
      const fresh = newWireOfSig(pre, post, relSig(args))
      return { rule: 'argContract', wire: fresh, position: step.position }
    }
    case 'applyFormal':
      return {
        rule: 'abstractFormal',
        ends: newNodes(),
        scope: derivedScope(pre, step.wire),
      }
    case 'identityLeaf':
      return {
        rule: 'identityAbstract',
        nodes: newNodes(),
        scope: derivedScope(pre, step.wire),
      }
    case 'refLeaf':
      return {
        rule: 'refAbstract',
        nodes: newNodes(),
        scope: derivedScope(pre, step.wire),
      }
    case 'wireJoin': {
      const dying = preWire(step.input.b)
      const survivorPost = post.wires[step.input.a] !== undefined
        ? step.input.a
        : step.input.b
      const movedKeys = new Set(dying.endpoints.map((endpoint) =>
        `${endpoint.node}|${endpoint.port.kind}|${
          endpoint.port.kind === 'head' ? '' : endpoint.port.index}`))
      const keep = post.wires[survivorPost]!.endpoints.filter((endpoint) =>
        !movedKeys.has(`${endpoint.node}|${endpoint.port.kind}|${
          endpoint.port.kind === 'head' ? '' : endpoint.port.index}`))
      return {
        rule: 'wireSever',
        input: {
          wire: survivorPost,
          keep,
          scope: derivedScope(pre, step.input.b),
        },
      }
    }
    default:
      break
  }
  throw new RuleError(`invert: no inverse for step '${step.rule}'`)
}

function fullReservation(diagram: Diagram): IdReservation {
  return {
    regions: new Set(Object.keys(diagram.regions)),
    nodes: new Set(Object.keys(diagram.nodes)),
    wires: new Set(Object.keys(diagram.wires)),
  }
}

function deletedStartIds(
  start: Diagram,
  traceDiffs: readonly { readonly before: Diagram; readonly after: Diagram }[],
): { regions: string[]; nodes: string[]; wires: string[] } {
  const deleted = { regions: new Set<string>(), nodes: new Set<string>(), wires: new Set<string>() }
  for (const { before, after } of traceDiffs) {
    for (const id of Object.keys(before.regions)) {
      if (after.regions[id] === undefined && start.regions[id] !== undefined) {
        deleted.regions.add(id)
      }
    }
    for (const id of Object.keys(before.nodes)) {
      if (after.nodes[id] === undefined && start.nodes[id] !== undefined) {
        deleted.nodes.add(id)
      }
    }
    for (const id of Object.keys(before.wires)) {
      if (after.wires[id] === undefined && start.wires[id] !== undefined) {
        deleted.wires.add(id)
      }
    }
  }
  return {
    regions: [...deleted.regions].sort(),
    nodes: [...deleted.nodes].sort(),
    wires: [...deleted.wires].sort(),
  }
}

/**
 * Compile a relation join as one durable action. Ids the action deletes are
 * excluded from re-minting via the action's allocation, so an id never
 * denotes two different objects across one action — diff-based selection
 * capture in authoring scripts stays sound.
 */
export function compileRelationJoinAction(
  label: string,
  diagram: Diagram,
  wire: WireId,
  content: DiagramWithBoundary,
  parameters: readonly WireId[],
  context: ProofContext,
  orientation: Orientation = 'forward',
): ProofAction {
  const diffs: Array<{ before: Diagram; after: Diagram }> = []
  compileRelationJoin(diagram, wire, content, parameters, context, orientation, {
    reservation: fullReservation(diagram),
    onStep: (_, before, after) => diffs.push({ before, after }),
  })
  const allocation = deletedStartIds(diagram, diffs)
  const steps = compileRelationJoin(
    diagram,
    wire,
    content,
    parameters,
    context,
    orientation,
    {
      reservation: {
        regions: new Set(allocation.regions),
        nodes: new Set(allocation.nodes),
        wires: new Set(allocation.wires),
      },
    },
  )
  return { label, steps, placements: [], allocation }
}

/** The sever counterpart of `compileRelationJoinAction`. */
export function compileRelationSeverAction(
  label: string,
  diagram: Diagram,
  input: RelationSeverInput,
  context: ProofContext,
  orientation: Orientation = 'forward',
): ProofAction {
  const first = compileRelationSever(diagram, input, context, orientation, {
    reservation: fullReservation(diagram),
  })
  const allocation = deletedStartIds(diagram, first.diffs)
  const second = compileRelationSever(diagram, input, context, orientation, {
    reservation: {
      regions: new Set(allocation.regions),
      nodes: new Set(allocation.nodes),
      wires: new Set(allocation.wires),
    },
  })
  return { label, steps: second.steps, placements: [], allocation }
}
