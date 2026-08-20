import type {
  Diagram,
  Endpoint,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { derivedScope, isAncestorOrEqual, polarity } from '../diagram/regions'
import { sigEquals, sigKey } from '../diagram/sig'
import { type IdReservation } from '../diagram/subgraph/freshId'
import { freshId } from '../diagram/subgraph/freshId'
import { completeWireEnds } from './wire-ends'
import { RuleError } from './error'

/**
 * Durable single-wire sever input. Splitting one wire's endpoint set into
 * two wires forgets the equality between the parts; the fresh wire's scope
 * may be chosen anywhere between the moved endpoints' DCA and the severed
 * wire's own derived scope (inclusive), and the choice is materialized as
 * pins by the completion clause — each side of the split is completed at
 * its declared scope until it has two ends.
 */
export type WireSeverInput = {
  readonly wire: WireId
  readonly keep: readonly Endpoint[]
  /**
   * Scope for the split-off wire. Must enclose every moved endpoint; the
   * polarity gate follows this region. Defaults to the wire's own derived
   * scope.
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
  const oldScope = derivedScope(d, input.wire)
  const freshScope = input.scope ?? oldScope
  if (d.regions[freshScope] === undefined) {
    throw new DiagramError(`unknown region '${freshScope}'`)
  }
  // The fresh wire is a new binder at-or-below the severed wire's own binder
  // (Lean: the new local lives in the region the rule is applied in). A
  // scope above it would hoist an existential over every intervening
  // quantifier and cut.
  if (!isAncestorOrEqual(d, oldScope, freshScope)) {
    throw new RuleError(
      `fresh wire scope '${freshScope}' does not lie within the scope `
      + `'${oldScope}' of wire '${input.wire}'`,
    )
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
  const parts = {
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires: {
      ...d.wires,
      [input.wire]: { sig: selected.sig, endpoints: kept },
      [fresh]: { sig: selected.sig, endpoints: moved },
    },
  }
  completeWireEnds(parts, fresh, freshScope, 'sever', reservation?.nodes)
  completeWireEnds(parts, input.wire, oldScope, 'sever', reservation?.nodes)
  return mkDiagram({ root: d.root, ...parts })
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

  const scopeA = derivedScope(d, input.a)
  const scopeB = derivedScope(d, input.b)
  let outerId: WireId
  let innerId: WireId
  if (isAncestorOrEqual(d, scopeA, scopeB)) {
    outerId = input.a
    innerId = input.b
  } else if (isAncestorOrEqual(d, scopeB, scopeA)) {
    outerId = input.b
    innerId = input.a
  } else {
    throw new RuleError(
      `wires '${input.a}' and '${input.b}' have incomparable scopes `
      + `('${scopeA}', '${scopeB}'); iterate one inward first`,
    )
  }
  const inner = d.wires[innerId]!
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, innerId === input.a ? scopeA : scopeB)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `joining wires requires the inner wire's scope to be ${need}; `
      + `'${innerId === input.a ? scopeA : scopeB}' is ${have}`,
    )
  }
  const outer = d.wires[outerId]!
  const wires: Record<WireId, Wire> = {}
  for (const [id, candidate] of Object.entries(d.wires)) {
    if (id === innerId) continue
    wires[id] = id === outerId
      ? {
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
