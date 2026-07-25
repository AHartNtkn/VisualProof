import { deserializeTerm, serializeTerm } from '../term/serialize'
import type { Diagram, Port, Region, DiagramNode, Wire } from './diagram'
import { mkDiagram, portKey } from './diagram'
import type { Sig, RelSig } from './sig'
import { IOTA, relSig, assertWellFormedSig } from './sig'
import type { DiagramWithBoundary } from './boundary'
import { mkDiagramWithBoundary } from './boundary'

/**
 * Pure-data JSON form of a diagram. Semantic content only — by the layer
 * separation edict there is nothing else to save. Terms are embedded as
 * injective term-serialization strings; ports as portKey strings; signatures
 * as their own recursive `{kind}` objects. Ids are preserved verbatim. Theory
 * files (Plan 5) wrap this in their own versioned envelope; this object carries
 * no version of its own.
 */
export function diagramToJson(d: Diagram): unknown {
  const regions: Record<string, unknown> = {}
  for (const [id, r] of Object.entries(d.regions)) regions[id] = { ...r }
  // Return-typed switch (no default): a new node kind forces a serialization here.
  const nodeToJson = (n: DiagramNode): Record<string, unknown> => {
    switch (n.kind) {
      case 'term': return { kind: 'term', region: n.region, term: serializeTerm(n.term), freePorts: [...n.freePorts] }
      case 'atom': return { kind: 'atom', region: n.region, sig: sigToJson(n.sig) }
      case 'ref': return { kind: 'ref', region: n.region, defId: n.defId, sig: sigToJson(n.sig) }
      case 'body': return { kind: 'body', region: n.region, sig: sigToJson(n.sig), content: dwbToJson(n.content) }
    }
  }
  const nodes: Record<string, unknown> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[id] = nodeToJson(n)
  }
  const wires: Record<string, unknown> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = {
      scope: w.scope,
      sig: sigToJson(w.sig),
      endpoints: w.endpoints.map((ep) => ({ node: ep.node, port: portKey(ep.port) })),
    }
  }
  return { root: d.root, regions, nodes, wires }
}

function fail(msg: string): never {
  throw new Error(`malformed diagram JSON: ${msg}`)
}

function assertOnlyKeys(v: Record<string, unknown>, allowed: readonly string[], what: string): void {
  for (const k of Object.keys(v)) {
    if (!allowed.includes(k)) fail(`${what} has unknown field '${k}' (semantic files carry no extra data)`)
  }
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v)
}

/** Canonical recursive JSON of a signature: `{kind:'iota'}` or `{kind:'rel',args}`. */
export function sigToJson(s: Sig): unknown {
  return s.kind === 'iota' ? { kind: 'iota' } : { kind: 'rel', args: s.args.map(sigToJson) }
}

/**
 * Decode an untrusted signature. Structural validity is enforced loudly by
 * `assertWellFormedSig`; strict key membership (no smuggled extra data) and
 * canonicalization into shared frozen values (`IOTA`, `relSig`) are enforced on
 * the way back out.
 */
export function sigFromJson(v: unknown, what: string): Sig {
  try {
    assertWellFormedSig(v)
  } catch (e) {
    fail(`${what} sig: ${e instanceof Error ? e.message : String(e)}`)
  }
  return rebuildSig(v as Sig, what)
}

function rebuildSig(s: Sig, what: string): Sig {
  if (s.kind === 'iota') {
    if (Object.keys(s).length !== 1) fail(`${what} sig: iota signature carries extra fields`)
    return IOTA
  }
  if (Object.keys(s).length !== 2) fail(`${what} sig: relation signature carries extra fields`)
  return relSig(s.args.map((a, i) => rebuildSig(a, `${what} sig arg ${i}`)))
}

/** Decode an untrusted signature that must be relational (atoms, refs, bodies). */
export function relSigFromJson(v: unknown, what: string): RelSig {
  const s = sigFromJson(v, what)
  if (s.kind !== 'rel') fail(`${what} sig must be a relation signature`)
  return s
}

/** A diagram plus an ordered boundary — the serialized form of a relation body
 * and of body-node content. Recursive: the diagram may itself carry body nodes. */
export function dwbToJson(dwb: DiagramWithBoundary): unknown {
  return { diagram: diagramToJson(dwb.diagram), boundary: [...dwb.boundary] }
}

export function dwbFromJson(v: unknown, what = 'pattern'): DiagramWithBoundary {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['diagram', 'boundary'], what)
  if (!Array.isArray(v.boundary) || !v.boundary.every((x) => typeof x === 'string')) {
    fail(`${what}.boundary must be an array of wire ids`)
  }
  try {
    return mkDiagramWithBoundary(diagramFromJson(v.diagram), v.boundary as string[])
  } catch (e) {
    return fail(`${what}: ${e instanceof Error ? e.message : String(e)}`)
  }
}

export function parsePortKey(key: string): Port {
  if (key === 'out') return { kind: 'output' }
  if (key === 'hd') return { kind: 'head' }
  if (key.startsWith('v:') && key.length > 2) return { kind: 'freeVar', name: key.slice(2) }
  if (key.startsWith('a:')) {
    const raw = key.slice(2)
    const n = Number(raw)
    // canonical form only: portKey emits plain decimal digits, never '1e2' etc.
    if (Number.isSafeInteger(n) && n >= 0 && String(n) === raw) return { kind: 'arg', index: n }
  }
  return fail(`unrecognized port key '${key}'`)
}

export function diagramFromJson(j: unknown): Diagram {
  if (!isRecord(j)) fail('top level must be an object')
  assertOnlyKeys(j, ['root', 'regions', 'nodes', 'wires'], 'top level')
  const { root, regions: jr, nodes: jn, wires: jw } = j
  if (typeof root !== 'string') fail("'root' must be a string")
  if (!isRecord(jr) || !isRecord(jn) || !isRecord(jw)) fail("'regions', 'nodes', 'wires' must be objects")

  const regions: Record<string, Region> = {}
  for (const [id, v] of Object.entries(jr)) {
    if (!isRecord(v)) fail(`region '${id}' must be an object`)
    if (v.kind === 'sheet') {
      assertOnlyKeys(v, ['kind'], `region '${id}'`)
      regions[id] = { kind: 'sheet' }
      continue
    }
    if (v.kind === 'cut' && typeof v.parent === 'string') {
      assertOnlyKeys(v, ['kind', 'parent'], `region '${id}'`)
      regions[id] = { kind: 'cut', parent: v.parent }
      continue
    }
    fail(`region '${id}' has unrecognized shape`)
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const [id, v] of Object.entries(jn)) {
    if (!isRecord(v) || typeof v.region !== 'string') fail(`node '${id}' has unrecognized shape`)
    if (v.kind === 'term' && typeof v.term === 'string'
      && Array.isArray(v.freePorts) && v.freePorts.every((name) => typeof name === 'string')) {
      assertOnlyKeys(v, ['kind', 'region', 'term', 'freePorts'], `node '${id}'`)
      try {
        nodes[id] = {
          kind: 'term',
          region: v.region,
          term: deserializeTerm(v.term),
          freePorts: v.freePorts as string[],
        }
      } catch (e) {
        fail(`node '${id}' term: ${e instanceof Error ? e.message : String(e)}`)
      }
      continue
    }
    if (v.kind === 'atom' && 'sig' in v) {
      assertOnlyKeys(v, ['kind', 'region', 'sig'], `node '${id}'`)
      nodes[id] = { kind: 'atom', region: v.region, sig: relSigFromJson(v.sig, `node '${id}'`) }
      continue
    }
    if (v.kind === 'ref' && typeof v.defId === 'string' && 'sig' in v) {
      assertOnlyKeys(v, ['kind', 'region', 'defId', 'sig'], `node '${id}'`)
      nodes[id] = { kind: 'ref', region: v.region, defId: v.defId, sig: relSigFromJson(v.sig, `node '${id}'`) }
      continue
    }
    if (v.kind === 'body' && 'sig' in v && 'content' in v) {
      assertOnlyKeys(v, ['kind', 'region', 'sig', 'content'], `node '${id}'`)
      nodes[id] = {
        kind: 'body',
        region: v.region,
        sig: relSigFromJson(v.sig, `node '${id}'`),
        content: dwbFromJson(v.content, `node '${id}' content`),
      }
      continue
    }
    fail(`node '${id}' has unrecognized shape`)
  }

  const wires: Record<string, Wire> = {}
  for (const [id, v] of Object.entries(jw)) {
    if (!isRecord(v) || typeof v.scope !== 'string' || !Array.isArray(v.endpoints)) {
      fail(`wire '${id}' has unrecognized shape`)
    }
    assertOnlyKeys(v, ['scope', 'sig', 'endpoints'], `wire '${id}'`)
    if (!('sig' in v)) fail(`wire '${id}' is missing its 'sig' field`)
    const sig = sigFromJson(v.sig, `wire '${id}'`)
    const endpoints = v.endpoints.map((ep, k) => {
      if (!isRecord(ep) || typeof ep.node !== 'string' || typeof ep.port !== 'string') {
        return fail(`wire '${id}' endpoint ${k} has unrecognized shape`)
      }
      assertOnlyKeys(ep, ['node', 'port'], `wire '${id}' endpoint ${k}`)
      return { node: ep.node, port: parsePortKey(ep.port) }
    })
    wires[id] = { scope: v.scope, sig, endpoints }
  }

  return mkDiagram({ root, regions, nodes, wires })
}
