import type { Diagram, DiagramNode, Port, Region, Wire } from './diagram'
import { mkDiagram, portKey } from './diagram'
import type { RelSig, Sig } from './sig'
import { assertWellFormedSig, IOTA, relSig } from './sig'
import type { DiagramWithBoundary } from './boundary'
import { mkDiagramWithBoundary } from './boundary'
import { deserializeTerm, serializeTerm } from '../term/serialize'

/** Serialize semantic diagram content with IDs preserved verbatim. */
export function diagramToJson(diagram: Diagram): unknown {
  const regions: Record<string, unknown> = {}
  for (const [id, region] of Object.entries(diagram.regions)) {
    regions[id] = { ...region }
  }

  const nodeToJson = (node: DiagramNode): Record<string, unknown> => {
    switch (node.kind) {
      case 'term':
        return {
          kind: 'term',
          region: node.region,
          term: serializeTerm(node.term),
          freeArity: node.freeArity,
        }
      case 'atom':
        return { kind: 'atom', region: node.region, sig: sigToJson(node.sig) }
      case 'ref':
        return {
          kind: 'ref',
          region: node.region,
          defId: node.defId,
          sig: sigToJson(node.sig),
        }
      case 'identity':
        return {
          kind: 'identity',
          region: node.region,
          sig: sigToJson(node.sig),
          arity: node.arity,
        }
    }
  }
  const nodes: Record<string, unknown> = {}
  for (const [id, node] of Object.entries(diagram.nodes)) {
    nodes[id] = nodeToJson(node)
  }

  const wires: Record<string, unknown> = {}
  for (const [id, wire] of Object.entries(diagram.wires)) {
    wires[id] = {
      sig: sigToJson(wire.sig),
      endpoints: wire.endpoints.map((endpoint) => ({
        node: endpoint.node,
        port: portKey(endpoint.port),
      })),
    }
  }
  return { root: diagram.root, regions, nodes, wires }
}

function fail(message: string): never {
  throw new Error(`malformed diagram JSON: ${message}`)
}

function assertOnlyKeys(
  value: Record<string, unknown>,
  allowed: readonly string[],
  what: string,
): void {
  for (const key of Object.keys(value)) {
    if (!allowed.includes(key)) {
      fail(`${what} has unknown field '${key}' (semantic files carry no extra data)`)
    }
  }
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value)
}

export function sigToJson(sig: Sig): unknown {
  return sig.kind === 'iota'
    ? { kind: 'iota' }
    : { kind: 'rel', args: sig.args.map(sigToJson) }
}

export function sigFromJson(value: unknown, what: string): Sig {
  try {
    assertWellFormedSig(value)
  } catch (error) {
    fail(`${what} sig: ${error instanceof Error ? error.message : String(error)}`)
  }
  return rebuildSig(value as Sig, what)
}

function rebuildSig(sig: Sig, what: string): Sig {
  if (sig.kind === 'iota') {
    if (Object.keys(sig).length !== 1) {
      fail(`${what} sig: iota signature carries extra fields`)
    }
    return IOTA
  }
  if (Object.keys(sig).length !== 2) {
    fail(`${what} sig: relation signature carries extra fields`)
  }
  return relSig(sig.args.map((argument, index) =>
    rebuildSig(argument, `${what} sig arg ${index}`),
  ))
}

export function relSigFromJson(value: unknown, what: string): RelSig {
  const sig = sigFromJson(value, what)
  if (sig.kind !== 'rel') fail(`${what} sig must be a relation signature`)
  return sig
}

export function dwbToJson(dwb: DiagramWithBoundary): unknown {
  return {
    diagram: diagramToJson(dwb.diagram),
    boundary: [...dwb.boundary],
  }
}

export function dwbFromJson(value: unknown, what = 'pattern'): DiagramWithBoundary {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['diagram', 'boundary'], what)
  if (
    !Array.isArray(value.boundary)
    || !value.boundary.every((wireId) => typeof wireId === 'string')
  ) {
    fail(`${what}.boundary must be an array of wire ids`)
  }
  try {
    return mkDiagramWithBoundary(
      rawDiagramFromJson(value.diagram),
      value.boundary as string[],
    )
  } catch (error) {
    return fail(`${what}: ${error instanceof Error ? error.message : String(error)}`)
  }
}

export function parsePortKey(key: string): Port {
  if (key === 'out') return { kind: 'output' }
  if (key === 'hd') return { kind: 'head' }
  for (const [prefix, kind] of [
    ['f:', 'free'],
    ['a:', 'arg'],
    ['i:', 'identity'],
  ] as const) {
    if (!key.startsWith(prefix)) continue
    const raw = key.slice(prefix.length)
    const index = Number(raw)
    if (
      Number.isSafeInteger(index)
      && index >= 0
      && String(index) === raw
    ) {
      return { kind, index }
    }
  }
  return fail(`unrecognized port key '${key}'`)
}

function rawDiagramFromJson(json: unknown): Diagram {
  if (!isRecord(json)) fail('top level must be an object')
  assertOnlyKeys(json, ['root', 'regions', 'nodes', 'wires'], 'top level')
  const { root, regions: jsonRegions, nodes: jsonNodes, wires: jsonWires } = json
  if (typeof root !== 'string') fail("'root' must be a string")
  if (!isRecord(jsonRegions) || !isRecord(jsonNodes) || !isRecord(jsonWires)) {
    fail("'regions', 'nodes', 'wires' must be objects")
  }

  const regions: Record<string, Region> = {}
  for (const [id, value] of Object.entries(jsonRegions)) {
    if (!isRecord(value)) fail(`region '${id}' must be an object`)
    if (value.kind === 'sheet') {
      assertOnlyKeys(value, ['kind'], `region '${id}'`)
      regions[id] = { kind: 'sheet' }
      continue
    }
    if (value.kind === 'cut' && typeof value.parent === 'string') {
      assertOnlyKeys(value, ['kind', 'parent'], `region '${id}'`)
      regions[id] = { kind: 'cut', parent: value.parent }
      continue
    }
    fail(`region '${id}' has unrecognized shape`)
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const [id, value] of Object.entries(jsonNodes)) {
    if (!isRecord(value) || typeof value.region !== 'string') {
      fail(`node '${id}' has unrecognized shape`)
    }
    if (
      value.kind === 'term'
      && typeof value.term === 'string'
      && typeof value.freeArity === 'number'
    ) {
      assertOnlyKeys(value, ['kind', 'region', 'term', 'freeArity'], `node '${id}'`)
      try {
        nodes[id] = {
          kind: 'term',
          region: value.region,
          term: deserializeTerm(value.term),
          freeArity: value.freeArity,
        }
      } catch (error) {
        fail(`node '${id}' term: ${error instanceof Error ? error.message : String(error)}`)
      }
      continue
    }
    if (value.kind === 'atom') {
      assertOnlyKeys(value, ['kind', 'region', 'sig'], `node '${id}'`)
      nodes[id] = {
        kind: 'atom',
        region: value.region,
        sig: relSigFromJson(value.sig, `node '${id}'`),
      }
      continue
    }
    if (value.kind === 'ref' && typeof value.defId === 'string') {
      assertOnlyKeys(value, ['kind', 'region', 'defId', 'sig'], `node '${id}'`)
      nodes[id] = {
        kind: 'ref',
        region: value.region,
        defId: value.defId,
        sig: relSigFromJson(value.sig, `node '${id}'`),
      }
      continue
    }
    if (value.kind === 'identity' && typeof value.arity === 'number') {
      assertOnlyKeys(value, ['kind', 'region', 'sig', 'arity'], `node '${id}'`)
      nodes[id] = {
        kind: 'identity',
        region: value.region,
        sig: sigFromJson(value.sig, `node '${id}'`),
        arity: value.arity,
      }
      continue
    }
    fail(`node '${id}' has unrecognized shape`)
  }

  const wires: Record<string, Wire> = {}
  for (const [id, value] of Object.entries(jsonWires)) {
    if (!isRecord(value) || !Array.isArray(value.endpoints)) {
      fail(`wire '${id}' has unrecognized shape`)
    }
    assertOnlyKeys(value, ['sig', 'endpoints'], `wire '${id}'`)
    wires[id] = {
      sig: sigFromJson(value.sig, `wire '${id}'`),
      endpoints: value.endpoints.map((endpoint, index) => {
        if (
          !isRecord(endpoint)
          || typeof endpoint.node !== 'string'
          || typeof endpoint.port !== 'string'
        ) {
          return fail(`wire '${id}' endpoint ${index} has unrecognized shape`)
        }
        assertOnlyKeys(endpoint, ['node', 'port'], `wire '${id}' endpoint ${index}`)
        return { node: endpoint.node, port: parsePortKey(endpoint.port) }
      }),
    }
  }

  return { root, regions, nodes, wires }
}

/**
 * Decode an ordinary closed diagram. Bounded interfaces use dwbFromJson,
 * whose boundary entries count toward each wire's two-end floor.
 */
export function diagramFromJson(json: unknown): Diagram {
  const raw = rawDiagramFromJson(json)
  try {
    return mkDiagram(raw)
  } catch (error) {
    return fail(error instanceof Error ? error.message : String(error))
  }
}
