import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import { exploreForm } from '../diagram/canonical/explore'
import type {
  Diagram,
  DiagramNode,
  Endpoint,
  RegionId,
  Wire,
  WireId,
} from '../diagram/diagram'
import { DiagramError, mkDiagram, portKey } from '../diagram/diagram'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import { IOTA, relSig, sigEquals, sigKey } from '../diagram/sig'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { freshId, type IdReservation } from '../diagram/subgraph/freshId'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import {
  selectionContents,
  type SelectionContents,
} from '../diagram/subgraph/selection'
import {
  removeSubgraph,
  spliceSubgraphMapped,
} from '../diagram/subgraph/splice'
import { RuleError } from './error'

export type ContentOccurrence = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

export type WireSeverInput =
  | {
      readonly kind: 'iota'
      readonly wire: WireId
      readonly keep: readonly Endpoint[]
    }
  | {
      readonly kind: 'relation'
      readonly scope: RegionId
      readonly occurrences: readonly ContentOccurrence[]
    }

export type WireJoinInput =
  | {
      readonly kind: 'iota'
      readonly a: WireId
      readonly b: WireId
    }
  | {
      readonly kind: 'relation'
      readonly wire: WireId
      readonly content: DiagramWithBoundary
      readonly parameters: readonly WireId[]
    }

type PreparedContent = {
  readonly pattern: DiagramWithBoundary
  readonly formalAttachments: readonly WireId[]
  readonly ambientAttachments: readonly WireId[]
}

type PreparedOccurrence = {
  readonly occurrence: ContentOccurrence
  readonly contents: SelectionContents
  readonly prepared: PreparedContent
}

type RelationApplication = {
  readonly node: string
  readonly region: RegionId
  readonly args: readonly WireId[]
}

function wire(d: Diagram, id: WireId): Wire {
  const result = d.wires[id]
  if (result === undefined) throw new DiagramError(`unknown wire '${id}'`)
  return result
}

function requireIota(w: Wire, id: WireId, operation: string): void {
  if (!sigEquals(w.sig, IOTA)) {
    throw new RuleError(
      `${operation} requires IOTA wire '${id}', got '${sigKey(w.sig)}'`,
    )
  }
}

function hasEndpoint(
  endpoints: readonly Endpoint[],
  candidate: Endpoint,
): boolean {
  return endpoints.some((endpoint) =>
    endpoint.node === candidate.node
    && portKey(endpoint.port) === portKey(candidate.port))
}

function applyIotaSever(
  d: Diagram,
  input: Extract<WireSeverInput, { readonly kind: 'iota' }>,
  orientation: 'forward' | 'backward',
  reservation?: IdReservation,
): Diagram {
  const selected = wire(d, input.wire)
  requireIota(selected, input.wire, 'iota wire sever')
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, selected.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `severing a wire requires a ${need} scope; `
      + `'${selected.scope}' is ${have}`,
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
        scope: selected.scope,
        sig: selected.sig,
        endpoints: moved,
      },
    },
  })
}

function applyIotaJoin(
  d: Diagram,
  input: Extract<WireJoinInput, { readonly kind: 'iota' }>,
  orientation: 'forward' | 'backward',
): Diagram {
  const a = wire(d, input.a)
  const b = wire(d, input.b)
  if (input.a === input.b) {
    throw new RuleError(`cannot join a wire with itself ('${input.a}')`)
  }
  requireIota(a, input.a, 'iota wire join')
  requireIota(b, input.b, 'iota wire join')

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

function intersects<T>(
  left: ReadonlySet<T>,
  right: ReadonlySet<T>,
): boolean {
  for (const item of left) {
    if (right.has(item)) return true
  }
  return false
}

function isEmpty(contents: SelectionContents): boolean {
  return contents.allRegions.size === 0
    && contents.allNodes.size === 0
    && contents.internalWires.length === 0
}

function assertDisjointOccurrences(
  occurrences: readonly {
    readonly occurrence: ContentOccurrence
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
        && isEmpty(left.contents)
        && isEmpty(right.contents)
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

function prepareContent(
  d: Diagram,
  occurrence: ContentOccurrence,
): PreparedContent {
  const extracted = extractSubgraph(d, occurrence.sel)
  const stubByAttachment = new Map<WireId, WireId>()
  extracted.attachments.forEach((attachment, index) => {
    stubByAttachment.set(attachment, extracted.pattern.boundary[index]!)
  })
  const formalBoundary = occurrence.args.map((attachment, index) => {
    wire(d, attachment)
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
  const ambientBoundary = ambientAttachments.map(
    (attachment) => stubByAttachment.get(attachment)!,
  )
  return {
    pattern: mkDiagramWithBoundary(
      extracted.pattern.diagram,
      [...formalBoundary, ...ambientBoundary],
    ),
    formalAttachments: Object.freeze([...occurrence.args]),
    ambientAttachments: Object.freeze([...ambientAttachments]),
  }
}

function assertPreparedCopies(
  d: Diagram,
  occurrences: readonly PreparedOccurrence[],
): void {
  const first = occurrences[0]!.prepared
  const firstFormalSignatures = first.formalAttachments.map(
    (attachment) => wire(d, attachment).sig,
  )
  const firstForm = exploreForm(
    first.pattern.diagram,
    first.pattern.boundary,
  )
  for (let occurrenceIndex = 1; occurrenceIndex < occurrences.length; occurrenceIndex++) {
    const candidate = occurrences[occurrenceIndex]!.prepared
    if (candidate.formalAttachments.length !== first.formalAttachments.length) {
      throw new RuleError(
        `occurrence ${occurrenceIndex} has ${candidate.formalAttachments.length} `
        + `formal arguments; expected ${first.formalAttachments.length}`,
      )
    }
    candidate.formalAttachments.forEach((attachment, argumentIndex) => {
      const actual = wire(d, attachment).sig
      const expected = firstFormalSignatures[argumentIndex]!
      if (!sigEquals(actual, expected)) {
        throw new RuleError(
          `formal argument ${argumentIndex} signature differs across `
          + `occurrences: '${sigKey(expected)}' vs '${sigKey(actual)}'`,
        )
      }
    })
    if (
      candidate.ambientAttachments.length !== first.ambientAttachments.length
      || candidate.ambientAttachments.some(
        (attachment, index) =>
          attachment !== first.ambientAttachments[index],
      )
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
}

function applyRelationSever(
  d: Diagram,
  input: Extract<WireSeverInput, { readonly kind: 'relation' }>,
  orientation: 'forward' | 'backward',
  reservation?: IdReservation,
): Diagram {
  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, input.scope)
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
    contents: selectionContents(d, occurrence.sel),
  }))
  assertDisjointOccurrences(contents)
  for (const { occurrence } of contents) {
    if (!isAncestorOrEqual(d, input.scope, occurrence.sel.region)) {
      throw new RuleError(
        `occurrence region '${occurrence.sel.region}' must descend from `
        + `quantifier scope '${input.scope}'`,
      )
    }
  }
  const prepared: PreparedOccurrence[] = contents.map((entry) => ({
    ...entry,
    prepared: prepareContent(d, entry.occurrence),
  }))
  assertPreparedCopies(d, prepared)

  for (const attachment of prepared[0]!.prepared.ambientAttachments) {
    const parameter = wire(d, attachment)
    if (!isAncestorOrEqual(d, parameter.scope, input.scope)) {
      throw new RuleError(
        `ambient attachment '${attachment}' scope '${parameter.scope}' `
        + `must enclose quantifier scope '${input.scope}'`,
      )
    }
  }

  let result = d
  for (const occurrence of input.occurrences) {
    result = removeSubgraph(result, occurrence.sel)
  }

  const quantifierSig = relSig(input.occurrences[0]!.args.map(
    (attachment) => wire(d, attachment).sig,
  ))
  const takenNodes = new Set(Object.keys(d.nodes))
  const takenWires = new Set(Object.keys(d.wires))
  const quantifierId = freshId(
    takenWires,
    'wire_quantifier',
    reservation?.wires,
  )
  const nodes: Record<string, DiagramNode> = { ...result.nodes }
  const wires: Record<WireId, Wire> = { ...result.wires }
  const quantifierEndpoints: Endpoint[] = []
  input.occurrences.forEach((occurrence, occurrenceIndex) => {
    const nodeId = freshId(
      takenNodes,
      `wire_quantifier_atom_${occurrenceIndex}`,
      reservation?.nodes,
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
        scope: existing.scope,
        sig: existing.sig,
        endpoints: [
          ...existing.endpoints,
          {
            node: nodeId,
            port: { kind: 'arg', index: argumentIndex },
          },
        ],
      }
    })
  })
  wires[quantifierId] = {
    scope: input.scope,
    sig: quantifierSig,
    endpoints: quantifierEndpoints,
  }
  return mkDiagram({
    root: result.root,
    regions: { ...result.regions },
    nodes,
    wires,
  })
}

function wireAtPort(
  d: Diagram,
  node: string,
  endpointPort: Endpoint['port'],
): WireId | undefined {
  const key = portKey(endpointPort)
  const matches = Object.entries(d.wires)
    .filter(([, candidate]) => candidate.endpoints.some(
      (endpoint) =>
        endpoint.node === node && portKey(endpoint.port) === key,
    ))
    .map(([id]) => id)
  return matches.length === 1 ? matches[0] : undefined
}

function collectApplications(
  d: Diagram,
  relationId: WireId,
  relation: Wire,
): readonly RelationApplication[] {
  const seen = new Set<string>()
  const applications: RelationApplication[] = []
  for (const endpoint of relation.endpoints) {
    if (endpoint.port.kind !== 'head') {
      throw new RuleError(
        `relation wire '${relationId}' endpoint '${endpoint.node}'/`
        + `'${portKey(endpoint.port)}' is not an atom head`,
      )
    }
    if (seen.has(endpoint.node)) {
      throw new RuleError(
        `relation wire '${relationId}' repeats atom-head endpoint `
        + `'${endpoint.node}'`,
      )
    }
    seen.add(endpoint.node)
    const node = d.nodes[endpoint.node]
    if (node === undefined || node.kind !== 'atom') {
      throw new RuleError(
        `relation wire '${relationId}' endpoint '${endpoint.node}' `
        + 'is not an atom head',
      )
    }
    if (!sigEquals(node.sig, relation.sig)) {
      throw new RuleError(
        `headed atom '${endpoint.node}' signature '${sigKey(node.sig)}' `
        + `does not match relation wire signature '${sigKey(relation.sig)}'`,
      )
    }
    if (!isAncestorOrEqual(d, relation.scope, node.region)) {
      throw new RuleError(
        `application '${endpoint.node}' is outside relation scope `
        + `'${relation.scope}'`,
      )
    }
    const args = relation.sig.kind === 'rel'
      ? relation.sig.args.map((expected, index) => {
          const argument = wireAtPort(
            d,
            endpoint.node,
            { kind: 'arg', index },
          )
          if (argument === undefined) {
            throw new RuleError(
              `headed atom '${endpoint.node}' is missing required `
              + `argument port ${index}`,
            )
          }
          const actual = d.wires[argument]!.sig
          if (!sigEquals(actual, expected)) {
            throw new RuleError(
              `headed atom '${endpoint.node}' argument port ${index} `
              + `has signature '${sigKey(actual)}'; expected `
              + `'${sigKey(expected)}'`,
            )
          }
          return argument
        })
      : []
    applications.push({
      node: endpoint.node,
      region: node.region,
      args,
    })
  }
  return applications.sort((left, right) =>
    left.node < right.node ? -1 : left.node > right.node ? 1 : 0)
}

function validatedContent(content: DiagramWithBoundary): DiagramWithBoundary {
  try {
    return mkDiagramWithBoundary(content.diagram, content.boundary)
  } catch (error) {
    throw new RuleError(
      `invalid relation grounding content: `
      + `${error instanceof Error ? error.message : String(error)}`,
    )
  }
}

function applyRelationJoin(
  d: Diagram,
  input: Extract<WireJoinInput, { readonly kind: 'relation' }>,
  orientation: 'forward' | 'backward',
  reservation?: IdReservation,
): Diagram {
  const relation = wire(d, input.wire)
  if (relation.sig.kind !== 'rel') {
    throw new RuleError(
      `relation wire join requires a relation wire, got `
      + `'${sigKey(relation.sig)}' on '${input.wire}'`,
    )
  }
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, relation.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}`
      + `relation wire join requires a ${need} scope; `
      + `'${relation.scope}' is ${have}`,
    )
  }

  const content = validatedContent(input.content)
  const arity = relation.sig.args.length
  if (content.boundary.length < arity) {
    throw new RuleError(
      `relation grounding content requires at least ${arity} boundary `
      + `positions for the formal arguments; got ${content.boundary.length}`,
    )
  }
  relation.sig.args.forEach((expected, index) => {
    const stubId = content.boundary[index]!
    const actual = content.diagram.wires[stubId]!.sig
    if (!sigEquals(actual, expected)) {
      throw new RuleError(
        `formal boundary position ${index} signature `
        + `'${sigKey(actual)}' does not match relation argument `
        + `'${sigKey(expected)}'`,
      )
    }
  })
  const suffix = content.boundary.slice(arity)
  if (suffix.length !== input.parameters.length) {
    throw new RuleError(
      `relation grounding boundary suffix has ${suffix.length} positions; `
      + `parameter count is ${input.parameters.length}`,
    )
  }
  if (input.parameters.includes(input.wire)) {
    throw new RuleError(
      `dying relation wire '${input.wire}' cannot be an ambient parameter`,
    )
  }
  input.parameters.forEach((parameterId, index) => {
    const parameter = wire(d, parameterId)
    const stubSig = content.diagram.wires[suffix[index]!]!.sig
    if (!sigEquals(parameter.sig, stubSig)) {
      throw new RuleError(
        `parameter ${index} wire '${parameterId}' signature `
        + `'${sigKey(parameter.sig)}' does not match boundary suffix `
        + `signature '${sigKey(stubSig)}'`,
      )
    }
    if (!isAncestorOrEqual(d, parameter.scope, relation.scope)) {
      throw new RuleError(
        `parameter '${parameterId}' scope '${parameter.scope}' must `
        + `enclose relation scope '${relation.scope}'`,
      )
    }
  })
  const applications = collectApplications(d, input.wire, relation)
  const spliceReservation: IdReservation = {
    regions: new Set([
      ...Object.keys(d.regions),
      ...(reservation?.regions ?? []),
    ]),
    nodes: new Set([
      ...Object.keys(d.nodes),
      ...(reservation?.nodes ?? []),
    ]),
    wires: new Set([
      ...Object.keys(d.wires),
      ...(reservation?.wires ?? []),
    ]),
  }

  let result = d
  for (const application of applications) {
    result = removeSubgraph(result, {
      region: application.region,
      regions: [],
      nodes: [application.node],
      wires: [],
    })
  }

  const attachmentImage = new Map<WireId, WireId>()
  const resolve = (id: WireId): WireId => {
    let current = id
    const visited = new Set<WireId>()
    while (attachmentImage.has(current)) {
      if (visited.has(current)) {
        throw new RuleError(
          `relation grounding attachment normalization cycles at '${current}'`,
        )
      }
      visited.add(current)
      current = attachmentImage.get(current)!
    }
    return current
  }

  for (const application of applications) {
    const attachments = [
      ...application.args.map(resolve),
      ...input.parameters.map(resolve),
    ]
    const spliced = spliceSubgraphMapped(
      result,
      application.region,
      content,
      attachments,
      { reserved: spliceReservation },
    )
    content.boundary.forEach((stub, index) => {
      const image = spliced.wireMap.get(stub)
      if (image === undefined) {
        throw new RuleError(
          `relation grounding splice did not retain boundary stub '${stub}'`,
        )
      }
      const attachment = attachments[index]!
      if (attachment !== image) attachmentImage.set(attachment, image)
    })
    result = spliced.diagram
  }

  const wires: Record<WireId, Wire> = {}
  for (const [id, candidate] of Object.entries(result.wires)) {
    if (id !== input.wire) wires[id] = candidate
  }
  return mkDiagram({
    root: result.root,
    regions: { ...result.regions },
    nodes: { ...result.nodes },
    wires,
  })
}

export function applyWireSever(
  diagram: Diagram,
  input: WireSeverInput,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  return input.kind === 'iota'
    ? applyIotaSever(diagram, input, orientation, reservation)
    : applyRelationSever(diagram, input, orientation, reservation)
}

export function applyWireJoin(
  diagram: Diagram,
  input: WireJoinInput,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  return input.kind === 'iota'
    ? applyIotaJoin(diagram, input, orientation)
    : applyRelationJoin(diagram, input, orientation, reservation)
}
