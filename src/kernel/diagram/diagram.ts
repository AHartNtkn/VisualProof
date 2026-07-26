import type { Sig, RelSig } from './sig'
import { assertWellFormedSig, sigEquals, sigKey } from './sig'
import { normalizeIdentities } from './canonical/identity'

export type RegionId = string
export type NodeId = string
export type WireId = string

export type Region =
  | { readonly kind: 'sheet' }
  | { readonly kind: 'cut'; readonly parent: RegionId }

export type IdentityDiagramNode = {
  readonly kind: 'identity'
  readonly region: RegionId
  readonly sig: Sig
  readonly arity: number
}

export type DiagramNode =
  | { readonly kind: 'atom'; readonly region: RegionId; readonly sig: RelSig }
  | { readonly kind: 'ref'; readonly region: RegionId; readonly defId: string; readonly sig: RelSig }
  | IdentityDiagramNode

export type Port =
  | { readonly kind: 'arg'; readonly index: number }
  | { readonly kind: 'head' }
  | { readonly kind: 'identity'; readonly index: number }

export type Endpoint = { readonly node: NodeId; readonly port: Port }

/**
 * One wire is one existentially scoped value of a fixed signature. Every
 * attached port must accept that signature.
 */
export type Wire = {
  readonly scope: RegionId
  readonly sig: Sig
  readonly endpoints: readonly Endpoint[]
}

export type Diagram = {
  readonly root: RegionId
  readonly regions: Readonly<Record<RegionId, Region>>
  readonly nodes: Readonly<Record<NodeId, DiagramNode>>
  readonly wires: Readonly<Record<WireId, Wire>>
}

export type DiagramParts = {
  readonly root: RegionId
  readonly regions: Record<RegionId, Region>
  readonly nodes?: Record<NodeId, DiagramNode>
  readonly wires?: Record<WireId, Wire>
}

export type DiagramNormalization = {
  readonly diagram: Diagram
  readonly wireImage: ReadonlyMap<WireId, WireId | undefined>
}

export type DiagramNormalizationCapture<T> = {
  readonly result: T
  readonly normalizations: readonly DiagramNormalization[]
}

const normalizationCaptures: DiagramNormalization[][] = []
let normalizationCaptureSuppression = 0

export class DiagramError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'DiagramError'
  }
}

export function portKey(port: Port): string {
  switch (port.kind) {
    case 'arg': return `a:${port.index}`
    case 'head': return 'hd'
    case 'identity': return `i:${port.index}`
  }
}

/** The exact storage ports a node must have attached. */
export function requiredPorts(node: DiagramNode): Port[] {
  switch (node.kind) {
    case 'atom':
      return [
        { kind: 'head' },
        ...node.sig.args.map((_, index): Port => ({ kind: 'arg', index })),
      ]
    case 'ref':
      return node.sig.args.map((_, index): Port => ({ kind: 'arg', index }))
    case 'identity':
      return Array.from(
        { length: node.arity },
        (_, index): Port => ({ kind: 'identity', index }),
      )
  }
}

/** The signature accepted by one concrete storage port. */
export function portSig(node: DiagramNode, port: Port): Sig {
  switch (node.kind) {
    case 'atom':
      if (port.kind === 'head') return node.sig
      if (port.kind === 'arg') {
        const sig = node.sig.args[port.index]
        if (sig !== undefined) return sig
      }
      break
    case 'ref':
      if (port.kind === 'arg') {
        const sig = node.sig.args[port.index]
        if (sig !== undefined) return sig
      }
      break
    case 'identity':
      if (
        port.kind === 'identity'
        && Number.isSafeInteger(port.index)
        && port.index >= 0
        && port.index < node.arity
      ) {
        return node.sig
      }
      break
  }
  throw new DiagramError(`node of kind '${node.kind}' has no port '${portKey(port)}'`)
}

function ancestorOrEqualRaw(
  regions: Readonly<Record<RegionId, Region>>,
  ancestor: RegionId,
  descendant: RegionId,
): boolean {
  let current = descendant
  for (;;) {
    if (current === ancestor) return true
    const region = regions[current]
    if (region === undefined || region.kind === 'sheet') return false
    current = region.parent
  }
}

function fail(message: string): never {
  throw new DiagramError(message)
}

/**
 * Validate and freeze a graph without normalizing it. The identity canonicalizer
 * uses this between rewrites, and bounded extraction uses it to preserve
 * equality evidence whose host scopes are temporarily outside the pattern.
 * Ordinary public construction goes through mkDiagramNormalized/mkDiagram.
 */
export function validateRawDiagram(raw: Diagram): Diagram {
  const rootId = raw.root
  const regions = raw.regions
  const nodes = raw.nodes
  const wires = raw.wires

  const root = regions[rootId] ?? fail(`root region '${rootId}' does not exist`)
  if (root.kind !== 'sheet') {
    fail(`root region '${rootId}' must be a sheet, got '${root.kind}'`)
  }

  for (const [id, region] of Object.entries(regions)) {
    if (region.kind === 'sheet' && id !== rootId) {
      fail(`region '${id}' is a second sheet; only the root may be a sheet`)
    }
    if (region.kind === 'cut' && regions[region.parent] === undefined) {
      fail(`region '${id}' has missing parent '${region.parent}'`)
    }
  }

  for (const id of Object.keys(regions)) {
    const seen = new Set<RegionId>()
    let current = id
    for (;;) {
      if (seen.has(current)) {
        fail(`region parent chain from '${id}' contains a cycle at '${current}'`)
      }
      seen.add(current)
      const region = regions[current]!
      if (region.kind === 'sheet') break
      current = region.parent
    }
  }

  const assertNodeSig = (id: NodeId, kind: DiagramNode['kind'], sig: Sig): void => {
    try {
      assertWellFormedSig(sig)
    } catch (error) {
      fail(`${kind} node '${id}' sig: ${error instanceof Error ? error.message : String(error)}`)
    }
  }

  for (const [id, node] of Object.entries(nodes)) {
    if (regions[node.region] === undefined) {
      fail(`node '${id}' is in missing region '${node.region}'`)
    }
    switch (node.kind) {
      case 'atom':
      case 'ref':
        assertNodeSig(id, node.kind, node.sig)
        if (node.sig.kind !== 'rel') {
          fail(`${node.kind} node '${id}' sig must be a relation signature, got '${sigKey(node.sig)}'`)
        }
        break
      case 'identity':
        assertNodeSig(id, node.kind, node.sig)
        if (!Number.isSafeInteger(node.arity) || node.arity < 2) {
          fail(`identity node '${id}' arity must be a safe integer at least 2, got '${String(node.arity)}'`)
        }
        break
      default:
        node satisfies never
        fail(`node '${id}' has an unrecognized kind`)
    }
  }

  const portsByNode = new Map<NodeId, Port[]>()
  for (const [id, node] of Object.entries(nodes)) {
    portsByNode.set(id, requiredPorts(node))
  }

  const attached = new Map<NodeId, Map<string, WireId>>()
  for (const [wireId, wire] of Object.entries(wires)) {
    try {
      assertWellFormedSig(wire.sig)
    } catch (error) {
      fail(`wire '${wireId}' sig: ${error instanceof Error ? error.message : String(error)}`)
    }
    if (regions[wire.scope] === undefined) {
      fail(`wire '${wireId}' has missing scope region '${wire.scope}'`)
    }
    for (const endpoint of wire.endpoints) {
      const node = nodes[endpoint.node]
        ?? fail(`wire '${wireId}' endpoint references missing node '${endpoint.node}'`)
      const key = portKey(endpoint.port)
      const required = portsByNode.get(endpoint.node)!
      if (!required.some((candidate) => portKey(candidate) === key)) {
        fail(`wire '${wireId}' endpoint references non-existent port '${key}' of node '${endpoint.node}'`)
      }
      const expected = portSig(node, endpoint.port)
      if (!sigEquals(wire.sig, expected)) {
        fail(
          `wire '${wireId}' sig '${sigKey(wire.sig)}' does not match port '${key}' `
          + `of node '${endpoint.node}' expecting '${sigKey(expected)}'`,
        )
      }
      let byPort = attached.get(endpoint.node)
      if (byPort === undefined) {
        byPort = new Map()
        attached.set(endpoint.node, byPort)
      }
      const previous = byPort.get(key)
      if (previous !== undefined) {
        fail(previous === wireId
          ? `port '${key}' of node '${endpoint.node}' appears more than once in wire '${wireId}'`
          : `port '${key}' of node '${endpoint.node}' is attached to two wires ('${previous}' and '${wireId}')`)
      }
      byPort.set(key, wireId)
      if (!ancestorOrEqualRaw(regions, wire.scope, node.region)) {
        fail(
          `wire '${wireId}' scope '${wire.scope}' does not enclose node `
          + `'${endpoint.node}' (region '${node.region}')`,
        )
      }
    }
  }

  for (const nodeId of Object.keys(nodes)) {
    for (const port of portsByNode.get(nodeId)!) {
      if (attached.get(nodeId)?.get(portKey(port)) === undefined) {
        fail(`port '${portKey(port)}' of node '${nodeId}' is not attached to any wire`)
      }
    }
  }

  return Object.freeze({
    root: rootId,
    regions: Object.freeze({ ...regions }),
    nodes: Object.freeze({ ...nodes }),
    wires: Object.freeze({ ...wires }),
  })
}

function rawFromParts(parts: DiagramParts): Diagram {
  return {
    root: parts.root,
    regions: parts.regions,
    nodes: parts.nodes ?? {},
    wires: parts.wires ?? {},
  }
}

/** Validate, eagerly normalize identities to a fixpoint, and retain transport. */
export function mkDiagramNormalized(parts: DiagramParts): DiagramNormalization {
  const normalization = normalizeIdentities(rawFromParts(parts))
  if (
    normalizationCaptureSuppression === 0
    && normalizationCaptures.length > 0
  ) {
    normalizationCaptures[normalizationCaptures.length - 1]!.push(
      normalization,
    )
  }
  return normalization
}

/** Canonical diagram construction when the caller does not need transport. */
export function mkDiagram(parts: DiagramParts): Diagram {
  return mkDiagramNormalized(parts).diagram
}

/**
 * Capture the authoritative wire images produced by one synchronous graph
 * mutation. Detached pattern construction may suppress capture explicitly.
 */
export function captureDiagramNormalizations<T>(
  operation: () => T,
): DiagramNormalizationCapture<T> {
  const normalizations: DiagramNormalization[] = []
  normalizationCaptures.push(normalizations)
  try {
    return {
      result: operation(),
      normalizations: Object.freeze([...normalizations]),
    }
  } finally {
    normalizationCaptures.pop()
  }
}

/** Exclude self-contained pattern normalization from a host mutation trace. */
export function withoutDiagramNormalizationCapture<T>(
  operation: () => T,
): T {
  normalizationCaptureSuppression += 1
  try {
    return operation()
  } finally {
    normalizationCaptureSuppression -= 1
  }
}
