import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type {
  Diagram,
  DiagramNode,
  NodeId,
  Region,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { exploreIso } from '../diagram/canonical/explore'
import { isAncestorOrEqual } from '../diagram/regions'
import type { RelSig, Sig } from '../diagram/sig'
import { relSig, sigEquals, sigKey } from '../diagram/sig'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { applyWireSever, type WireSeverInput } from '../rules/wire-quantifier'
import { RuleError } from '../rules/error'
import { mapStepIds } from './compose'
import type { ProofContext } from './context'
import { applyStep, type ProofStep } from './step'

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
  return Object.entries(content.diagram.wires)
    .filter(([wireId, wire]) =>
      wire.scope === content.diagram.root && !stubs.has(wireId))
    .map(([wireId]) => wireId)
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
  return Object.entries(content.diagram.nodes)
    .filter(([, node]) => node.region === content.diagram.root)
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
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (stubs.has(wireId)) {
      wires[wireId] = {
        scope: wire.scope,
        sig: wire.sig,
        endpoints: wire.endpoints.filter((endpoint) =>
          nodes[endpoint.node] !== undefined),
      }
    } else if (regions[wire.scope] !== undefined && wire.scope !== diagram.root) {
      wires[wireId] = wire
    }
  }
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
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (new Set(content.boundary).has(wireId)) {
      wires[wireId] = { scope: cut, sig: wire.sig, endpoints: wire.endpoints }
    } else if (subtree.has(wire.scope)) {
      wires[wireId] = wire
    }
  }
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
            input: { kind: 'iota', a: host, b: wire },
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
      const wire = plumb(emitter, residual, attachments.args)
      emitter.emit({ rule: 'identityLeaf', wire })
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
    emitter.emit({ rule: 'vacuousElim', wireId: residual.wire })
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
export function compileRelationJoin(
  diagram: Diagram,
  wire: WireId,
  content: DiagramWithBoundary,
  parameters: readonly WireId[],
  context: ProofContext,
  orientation: Orientation = 'forward',
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
    if (!isAncestorOrEqual(diagram, hostWire.scope, relation.scope)) {
      throw new RuleError(
        `parameter '${host}' scope '${hostWire.scope}' must enclose relation `
        + `scope '${relation.scope}'`,
      )
    }
    ambients.set(stub, host)
  })

  const steps: ProofStep[] = []
  let current = diagram
  const emitter: Emitter = {
    current: () => current,
    emit: (step) => {
      current = applyStep(current, step, context, orientation)
      steps.push(step)
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

/**
 * Compile a monolithic relation sever into primitive steps: plan the inverse
 * join against the (virtually) severed diagram, then emit each planned
 * step's inverse in reverse order, transporting ids through per-step
 * isomorphisms into the caller's real diagram.
 */
export function compileRelationSever(
  diagram: Diagram,
  input: Extract<WireSeverInput, { readonly kind: 'relation' }>,
  context: ProofContext,
  orientation: Orientation = 'forward',
): ProofStep[] {
  const severed = applyWireSever(diagram, input, orientation)
  const wire = newWireOfSig(
    diagram,
    severed,
    relSig(input.occurrences[0]!.args.map((attachment) => {
      const argWire = diagram.wires[attachment]
      if (argWire === undefined) {
        throw new RuleError(`unknown formal argument wire '${attachment}'`)
      }
      return argWire.sig
    })),
  )

  const extracted = extractSubgraph(diagram, input.occurrences[0]!.sel)
  const stubByAttachment = new Map<WireId, WireId>()
  extracted.attachments.forEach((attachment, index) => {
    stubByAttachment.set(attachment, extracted.pattern.boundary[index]!)
  })
  const formalBoundary = input.occurrences[0]!.args.map((attachment) => {
    const stub = stubByAttachment.get(attachment)
    if (stub === undefined) {
      throw new RuleError(
        `formal argument wire '${attachment}' does not touch the selected content`,
      )
    }
    return stub
  })
  const formalSet = new Set(input.occurrences[0]!.args)
  const ambientAttachments = extracted.attachments.filter(
    (attachment) => !formalSet.has(attachment),
  )
  const pattern = mkDiagramWithBoundary(
    extracted.pattern.diagram,
    [
      ...formalBoundary,
      ...ambientAttachments.map((attachment) => stubByAttachment.get(attachment)!),
    ],
  )

  const trace: Array<{ step: ProofStep; pre: Diagram; post: Diagram }> = []
  const joinOrientation: Orientation =
    orientation === 'forward' ? 'backward' : 'forward'
  {
    let current = severed
    const steps = compileRelationJoin(
      severed,
      wire,
      pattern,
      ambientAttachments,
      context,
      joinOrientation,
    )
    for (const step of steps) {
      const next = applyStep(current, step, context, joinOrientation)
      trace.push({ step, pre: current, post: next })
      current = next
    }
    const finalIso = exploreIso(current, diagram)
    if (finalIso === null) {
      throw new RuleError(
        'sever compilation failed: the planned join does not reproduce the diagram',
      )
    }
  }

  const output: ProofStep[] = []
  let real = diagram
  for (let index = trace.length - 1; index >= 0; index -= 1) {
    const { step, pre, post } = trace[index]!
    const iso = exploreIso(post, real)
    if (iso === null) {
      throw new RuleError(
        `sever compilation lost the isomorphism before inverting step ${index}`,
      )
    }
    const inverse = invertStep(step, pre, post)
    const mapped = mapStepIds(inverse, iso)
    real = applyStep(real, mapped, context, orientation)
    output.push(mapped)
  }
  return output
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
  const newNodes = (): NodeId[] =>
    Object.keys(post.nodes).filter((nodeId) => pre.nodes[nodeId] === undefined)
  const endArgs = (diagram: Diagram, nodeId: NodeId, arity: number): WireId[] =>
    Array.from({ length: arity }, (_, index) => {
      for (const [wireId, wireValue] of Object.entries(diagram.wires)) {
        if (wireValue.endpoints.some((endpoint) =>
          endpoint.node === nodeId
          && endpoint.port.kind === 'arg'
          && endpoint.port.index === index)) return wireId
      }
      throw new RuleError(`invert: end '${nodeId}' lacks argument ${index}`)
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
        sites: old.endpoints.map((endpoint) => ({
          region: pre.nodes[endpoint.node]!.region,
          args: endArgs(pre, endpoint.node, oldSig.args.length),
        })),
      }
    }
    case 'vacuousElim': {
      const old = preWire(step.wireId)
      return { rule: 'vacuousIntro', scope: old.scope, sig: old.sig }
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
      const preEnds = old.endpoints.map((endpoint) => endpoint.node)
      const postEnds = post.wires[fresh]!.endpoints.map((endpoint) => endpoint.node)
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
    case 'applyFormal': {
      const old = preWire(step.wire)
      return {
        rule: 'abstractFormal',
        ends: newNodes(),
        scope: old.scope,
      }
    }
    case 'identityLeaf': {
      const old = preWire(step.wire)
      return {
        rule: 'identityAbstract',
        nodes: newNodes(),
        scope: old.scope,
      }
    }
    case 'refLeaf': {
      const old = preWire(step.wire)
      return {
        rule: 'refAbstract',
        nodes: newNodes(),
        scope: old.scope,
      }
    }
    case 'wireJoin': {
      if (step.input.kind !== 'iota') break
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
          kind: 'iota',
          wire: survivorPost,
          keep,
          scope: dying.scope,
        },
      }
    }
    default:
      break
  }
  throw new RuleError(`invert: no inverse for step '${step.rule}'`)
}
