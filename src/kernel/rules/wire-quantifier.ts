import type {
  Diagram,
  Endpoint,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Durable single-wire sever input. Splitting one wire's endpoint set into
 * two wires forgets the equality between the parts; the fresh wire's scope
 * may be chosen anywhere enclosing the moved endpoints.
 */
export type WireSeverInput = {
  readonly wire: WireId
  readonly keep: readonly Endpoint[]
  /**
   * Scope for the split-off wire. Must enclose every moved endpoint; the
   * polarity gate follows this region. Defaults to the wire's own scope.
   */
  readonly scope?: RegionId
}

/** Durable single-wire join input: merge two co-signature wires into one. */
export type WireJoinInput = {
  readonly a: WireId
  readonly b: WireId
}

function wire(d: Diagram, id: WireId): Wire {
  const result = d.wires[id]
  if (result === undefined) throw new DiagramError(`unknown wire '${id}'`)
  return result
}

function hasEndpoint(
  endpoints: readonly Endpoint[],
  candidate: Endpoint,
): boolean {
  return endpoints.some((endpoint) =>
    endpoint.node === candidate.node
    && portKey(endpoint.port) === portKey(candidate.port))
}

export function applyWireSever(
  d: Diagram,
  input: WireSeverInput,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const selected = wire(d, input.wire)
  const freshScope = input.scope ?? selected.scope
  if (d.regions[freshScope] === undefined) {
    throw new DiagramError(`unknown region '${freshScope}'`)
  }
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, freshScope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `severing a wire requires a ${need} scope; `
      + `'${freshScope}' is ${have}`,
    )
  }
  for (const endpoint of input.keep) {
    if (!hasEndpoint(selected.endpoints, endpoint)) {
      throw new RuleError(
        `endpoint '${endpoint.node}'/'${portKey(endpoint.port)}' `
        + `is not an endpoint of wire '${input.wire}'`,
      )
    }
  }
  const kept = selected.endpoints.filter((endpoint) =>
    hasEndpoint(input.keep, endpoint))
  const moved = selected.endpoints.filter((endpoint) =>
    !hasEndpoint(input.keep, endpoint))
  for (const endpoint of moved) {
    const region = d.nodes[endpoint.node]!.region
    if (!isAncestorOrEqual(d, freshScope, region)) {
      throw new RuleError(
        `fresh wire scope '${freshScope}' does not enclose moved endpoint `
        + `'${endpoint.node}' in region '${region}'`,
      )
    }
  }
  const fresh = freshId(
    new Set(Object.keys(d.wires)),
    `${input.wire}_sever`,
    reservation?.wires,
  )
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires: {
      ...d.wires,
      [input.wire]: {
        scope: selected.scope,
        sig: selected.sig,
        endpoints: kept,
      },
      [fresh]: {
        scope: freshScope,
        sig: selected.sig,
        endpoints: moved,
      },
    },
  })
}

export function applyWireJoin(
  d: Diagram,
  input: WireJoinInput,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  const a = wire(d, input.a)
  const b = wire(d, input.b)
  if (input.a === input.b) {
    throw new RuleError(`cannot join a wire with itself ('${input.a}')`)
  }
  if (!sigEquals(a.sig, b.sig)) {
    throw new RuleError(
      `joining wires requires equal signatures; `
      + `'${input.a}' has '${sigKey(a.sig)}' but '${input.b}' has '${sigKey(b.sig)}'`,
    )
  }

  let outerId: WireId
  let innerId: WireId
  if (isAncestorOrEqual(d, a.scope, b.scope)) {
    outerId = input.a
    innerId = input.b
  } else if (isAncestorOrEqual(d, b.scope, a.scope)) {
    outerId = input.b
    innerId = input.a
  } else {
    throw new RuleError(
      `wires '${input.a}' and '${input.b}' have incomparable scopes `
      + `('${a.scope}', '${b.scope}'); iterate one inward first`,
    )
  }
  const inner = d.wires[innerId]!
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, inner.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `joining wires requires the inner wire's scope to be ${need}; `
      + `'${inner.scope}' is ${have}`,
    )
  }
  const outer = d.wires[outerId]!
  const wires: Record<WireId, Wire> = {}
  for (const [id, candidate] of Object.entries(d.wires)) {
    if (id === innerId) continue
    wires[id] = id === outerId
      ? {
          scope: outer.scope,
          sig: outer.sig,
          endpoints: [...outer.endpoints, ...inner.endpoints],
        }
      : candidate
  }
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires,
  })
}
