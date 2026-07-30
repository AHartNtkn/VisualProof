import type { Endpoint } from '../diagram/diagram'
import { portKey } from '../diagram/diagram'
import {
  dwbFromJson,
  dwbToJson,
  parsePortKey,
  relSigFromJson,
  sigFromJson,
  sigToJson,
} from '../diagram/json'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { IdentityRetarget } from '../rules/iteration'
import type {
  ContentOccurrence,
  WireJoinInput,
  WireSeverInput,
} from '../rules/wire-quantifier'
import type { PlacementHint, ProofAction, ProofAllocation } from './action'
import type { ProofStep } from './step'
import type { Theorem, TheoremApplication } from './theorem'

function fail(message: string): never {
  throw new Error(`malformed proof JSON: ${message}`)
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value)
}

function assertOnlyKeys(
  value: Record<string, unknown>,
  allowed: readonly string[],
  what: string,
): void {
  for (const key of Object.keys(value)) {
    if (!allowed.includes(key)) {
      fail(`${what} has unknown field '${key}'`)
    }
  }
}

function str(value: unknown, what: string): string {
  if (typeof value !== 'string') fail(`${what} must be a string`)
  return value
}

function strArray(value: unknown, what: string): string[] {
  if (!Array.isArray(value)) fail(`${what} must be an array`)
  return value.map((item, index) => str(item, `${what}[${index}]`))
}

function nonNegativeSafeInteger(value: unknown, what: string): number {
  if (
    typeof value !== 'number'
    || !Number.isSafeInteger(value)
    || value < 0
  ) {
    fail(`${what} must be a non-negative safe integer`)
  }
  return value
}

function selectionToJson(selection: SubgraphSelection): unknown {
  return {
    region: selection.region,
    regions: [...selection.regions],
    nodes: [...selection.nodes],
    wires: [...selection.wires],
  }
}

function selectionFromJson(
  value: unknown,
  what: string,
): SubgraphSelection {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['region', 'regions', 'nodes', 'wires'], what)
  return {
    region: str(value.region, `${what}.region`),
    regions: strArray(value.regions, `${what}.regions`),
    nodes: strArray(value.nodes, `${what}.nodes`),
    wires: strArray(value.wires, `${what}.wires`),
  }
}

function endpointToJson(endpoint: Endpoint): unknown {
  return { node: endpoint.node, port: portKey(endpoint.port) }
}

function endpointFromJson(value: unknown, what: string): Endpoint {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['node', 'port'], what)
  return {
    node: str(value.node, `${what}.node`),
    port: parsePortKey(str(value.port, `${what}.port`)),
  }
}

function contentOccurrenceToJson(
  occurrence: ContentOccurrence,
): unknown {
  return {
    sel: selectionToJson(occurrence.sel),
    args: [...occurrence.args],
  }
}

function contentOccurrenceFromJson(
  value: unknown,
  what: string,
): ContentOccurrence {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['sel', 'args'], what)
  return {
    sel: selectionFromJson(value.sel, `${what}.sel`),
    args: strArray(value.args, `${what}.args`),
  }
}

function wireSeverInputToJson(input: WireSeverInput): unknown {
  switch (input.kind) {
    case 'iota':
      return {
        kind: input.kind,
        wire: input.wire,
        keep: input.keep.map(endpointToJson),
      }
    case 'relation':
      return {
        kind: input.kind,
        scope: input.scope,
        occurrences: input.occurrences.map(contentOccurrenceToJson),
      }
  }
}

function wireSeverInputFromJson(value: unknown): WireSeverInput {
  if (!isRecord(value)) fail('wireSever input must be an object')
  const kind = str(value.kind, 'wireSever input.kind')
  switch (kind) {
    case 'iota':
      assertOnlyKeys(
        value,
        ['kind', 'wire', 'keep'],
        'wireSever iota input',
      )
      if (!Array.isArray(value.keep)) {
        fail('wireSever iota input.keep must be an array')
      }
      return {
        kind,
        wire: str(value.wire, 'wireSever input.wire'),
        keep: value.keep.map((endpoint, index) =>
          endpointFromJson(endpoint, `wireSever input.keep[${index}]`)),
      }
    case 'relation':
      assertOnlyKeys(
        value,
        ['kind', 'scope', 'occurrences'],
        'wireSever relation input',
      )
      if (!Array.isArray(value.occurrences)) {
        fail('wireSever relation input.occurrences must be an array')
      }
      return {
        kind,
        scope: str(value.scope, 'wireSever input.scope'),
        occurrences: value.occurrences.map((occurrence, index) =>
          contentOccurrenceFromJson(
            occurrence,
            `wireSever input.occurrences[${index}]`,
          )),
      }
    default:
      fail("wireSever input.kind must be 'iota'|'relation'")
  }
}

function wireJoinInputToJson(input: WireJoinInput): unknown {
  switch (input.kind) {
    case 'iota':
      return { kind: input.kind, a: input.a, b: input.b }
    case 'relation':
      return {
        kind: input.kind,
        wire: input.wire,
        content: dwbToJson(input.content),
        parameters: [...input.parameters],
      }
  }
}

function wireJoinInputFromJson(value: unknown): WireJoinInput {
  if (!isRecord(value)) fail('wireJoin input must be an object')
  const kind = str(value.kind, 'wireJoin input.kind')
  switch (kind) {
    case 'iota':
      assertOnlyKeys(value, ['kind', 'a', 'b'], 'wireJoin iota input')
      return {
        kind,
        a: str(value.a, 'wireJoin input.a'),
        b: str(value.b, 'wireJoin input.b'),
      }
    case 'relation':
      assertOnlyKeys(
        value,
        ['kind', 'wire', 'content', 'parameters'],
        'wireJoin relation input',
      )
      return {
        kind,
        wire: str(value.wire, 'wireJoin input.wire'),
        content: dwbFromJson(value.content, 'wireJoin input.content'),
        parameters: strArray(
          value.parameters,
          'wireJoin input.parameters',
        ),
      }
    default:
      fail("wireJoin input.kind must be 'iota'|'relation'")
  }
}

function idMapToJson(map: ReadonlyMap<string, string>): unknown {
  return [...map]
}

function idMapFromJson(value: unknown, what: string): Map<string, string> {
  if (!Array.isArray(value)) fail(`${what} must be an array`)
  const result = new Map<string, string>()
  for (const [index, entry] of value.entries()) {
    if (!Array.isArray(entry) || entry.length !== 2) {
      fail(`${what}[${index}] must be a [pattern, host] pair`)
    }
    const pattern = str(entry[0], `${what}[${index}][0]`)
    const host = str(entry[1], `${what}[${index}][1]`)
    if (result.has(pattern)) {
      fail(`${what} repeats pattern id '${pattern}'`)
    }
    result.set(pattern, host)
  }
  return result
}

function occurrenceCertificateToJson(
  certificate: OccurrenceCertificate,
): unknown {
  return {
    region: certificate.region,
    regionMap: idMapToJson(certificate.regionMap),
    nodeMap: idMapToJson(certificate.nodeMap),
    wireMap: idMapToJson(certificate.wireMap),
    attachments: [...certificate.attachments],
  }
}

function occurrenceCertificateFromJson(
  value: unknown,
  what: string,
): OccurrenceCertificate {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(
    value,
    ['region', 'regionMap', 'nodeMap', 'wireMap', 'attachments'],
    what,
  )
  return {
    region: str(value.region, `${what}.region`),
    regionMap: idMapFromJson(value.regionMap, `${what}.regionMap`),
    nodeMap: idMapFromJson(value.nodeMap, `${what}.nodeMap`),
    wireMap: idMapFromJson(value.wireMap, `${what}.wireMap`),
    attachments: strArray(value.attachments, `${what}.attachments`),
  }
}

function retargetToJson(retarget: IdentityRetarget): unknown {
  return {
    boundary: retarget.boundary,
    identity: retarget.identity,
    from: retarget.from,
    to: retarget.to,
  }
}

function retargetFromJson(value: unknown, what: string): IdentityRetarget {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['boundary', 'identity', 'from', 'to'], what)
  return {
    boundary: nonNegativeSafeInteger(value.boundary, `${what}.boundary`),
    identity: str(value.identity, `${what}.identity`),
    from: str(value.from, `${what}.from`),
    to: str(value.to, `${what}.to`),
  }
}

function retargetsFromJson(value: unknown, what: string): IdentityRetarget[] {
  if (!Array.isArray(value)) fail(`${what} must be an array`)
  return value.map((retarget, index) =>
    retargetFromJson(retarget, `${what}[${index}]`))
}

function applicationToJson(application: TheoremApplication): unknown {
  return {
    sel: selectionToJson(application.sel),
    args: [...application.args],
  }
}

function applicationFromJson(
  value: unknown,
  what: string,
): TheoremApplication {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['sel', 'args'], what)
  return {
    sel: selectionFromJson(value.sel, `${what}.sel`),
    args: strArray(value.args, `${what}.args`),
  }
}

export function stepToJson(step: ProofStep): unknown {
  switch (step.rule) {
    case 'refSpawn':
      return {
        rule: step.rule,
        region: step.region,
        defId: step.defId,
        sig: sigToJson(step.sig),
      }
    case 'atomSpawn':
      return { rule: step.rule, region: step.region, wire: step.wire }
    case 'identityInsert':
      return {
        rule: step.rule,
        region: step.region,
        wires: [...step.wires],
      }
    case 'wireJoin':
      return {
        rule: step.rule,
        input: wireJoinInputToJson(step.input),
      }
    case 'erasure':
      return { rule: step.rule, sel: selectionToJson(step.sel) }
    case 'wireSever':
      return {
        rule: step.rule,
        input: wireSeverInputToJson(step.input),
      }
    case 'iteration':
      return {
        rule: step.rule,
        sel: selectionToJson(step.sel),
        target: step.target,
        retargets: step.retargets.map(retargetToJson),
      }
    case 'deiteration':
      return {
        rule: step.rule,
        sel: selectionToJson(step.sel),
        justifier: selectionToJson(step.justifier),
        certificate: occurrenceCertificateToJson(step.certificate),
        retargets: step.retargets.map(retargetToJson),
      }
    case 'doubleCutIntro':
      return { rule: step.rule, sel: selectionToJson(step.sel) }
    case 'doubleCutElim':
      return { rule: step.rule, region: step.region }
    case 'theorem':
      return {
        rule: step.rule,
        name: step.name,
        at: applicationToJson(step.at),
        direction: step.direction,
      }
    case 'vacuousIntro':
      return {
        rule: step.rule,
        scope: step.scope,
        sig: sigToJson(step.sig),
      }
    case 'vacuousElim':
      return { rule: step.rule, wireId: step.wireId }
    case 'unfold':
      return { rule: step.rule, nodeId: step.nodeId }
    case 'fold':
      return {
        rule: step.rule,
        occurrence: selectionToJson(step.occurrence),
        args: [...step.args],
        defId: step.defId,
      }
    case 'cutWrap':
    case 'cutAbsorb':
    case 'parallelSplit':
    case 'endsDelete':
      return { rule: step.rule, wire: step.wire }
    case 'parallelFuse':
      return { rule: step.rule, a: step.a, b: step.b }
    case 'endsSpawn':
      return {
        rule: step.rule,
        wire: step.wire,
        sites: step.sites.map((site) => ({
          region: site.region,
          args: [...site.args],
        })),
      }
    case 'arityShift':
      return {
        rule: step.rule,
        wire: step.wire,
        newArgSig: sigToJson(step.newArgSig),
      }
    case 'arityUnshift':
    case 'argDuplicate':
    case 'argContract':
    case 'argDrop':
    case 'applyFormal':
      return { rule: step.rule, wire: step.wire, position: step.position }
    case 'argPermute':
      return {
        rule: step.rule,
        wire: step.wire,
        permutation: [...step.permutation],
      }
    case 'argExtend':
      return {
        rule: step.rule,
        wire: step.wire,
        position: step.position,
        newArgSig: sigToJson(step.newArgSig),
        attachments: { ...step.attachments },
      }
    case 'abstractFormal':
      return { rule: step.rule, ends: [...step.ends], scope: step.scope }
    case 'identityLeaf':
      return { rule: step.rule, wire: step.wire }
    case 'identityAbstract':
      return { rule: step.rule, nodes: [...step.nodes], scope: step.scope }
    case 'refLeaf':
      return { rule: step.rule, wire: step.wire, defId: step.defId }
    case 'refAbstract':
      return { rule: step.rule, nodes: [...step.nodes], scope: step.scope }
  }
}

export function stepFromJson(value: unknown): ProofStep {
  if (!isRecord(value)) fail('step must be an object')
  const rule = str(value.rule, 'step.rule')
  switch (rule) {
    case 'refSpawn':
      assertOnlyKeys(value, ['rule', 'region', 'defId', 'sig'], 'refSpawn step')
      return {
        rule,
        region: str(value.region, 'region'),
        defId: str(value.defId, 'defId'),
        sig: relSigFromJson(value.sig, 'sig'),
      }
    case 'atomSpawn':
      assertOnlyKeys(value, ['rule', 'region', 'wire'], 'atomSpawn step')
      return {
        rule,
        region: str(value.region, 'region'),
        wire: str(value.wire, 'wire'),
      }
    case 'identityInsert':
      assertOnlyKeys(value, ['rule', 'region', 'wires'], 'identityInsert step')
      return {
        rule,
        region: str(value.region, 'region'),
        wires: strArray(value.wires, 'wires'),
      }
    case 'wireJoin':
      assertOnlyKeys(value, ['rule', 'input'], 'wireJoin step')
      return { rule, input: wireJoinInputFromJson(value.input) }
    case 'erasure':
      assertOnlyKeys(value, ['rule', 'sel'], 'erasure step')
      return { rule, sel: selectionFromJson(value.sel, 'sel') }
    case 'wireSever':
      assertOnlyKeys(value, ['rule', 'input'], 'wireSever step')
      return { rule, input: wireSeverInputFromJson(value.input) }
    case 'iteration':
      assertOnlyKeys(
        value,
        ['rule', 'sel', 'target', 'retargets'],
        'iteration step',
      )
      return {
        rule,
        sel: selectionFromJson(value.sel, 'sel'),
        target: str(value.target, 'target'),
        retargets: retargetsFromJson(value.retargets, 'retargets'),
      }
    case 'deiteration':
      assertOnlyKeys(
        value,
        ['rule', 'sel', 'justifier', 'certificate', 'retargets'],
        'deiteration step',
      )
      return {
        rule,
        sel: selectionFromJson(value.sel, 'sel'),
        justifier: selectionFromJson(value.justifier, 'justifier'),
        certificate: occurrenceCertificateFromJson(
          value.certificate,
          'certificate',
        ),
        retargets: retargetsFromJson(value.retargets, 'retargets'),
      }
    case 'doubleCutIntro':
      assertOnlyKeys(value, ['rule', 'sel'], 'doubleCutIntro step')
      return { rule, sel: selectionFromJson(value.sel, 'sel') }
    case 'doubleCutElim':
      assertOnlyKeys(value, ['rule', 'region'], 'doubleCutElim step')
      return { rule, region: str(value.region, 'region') }
    case 'theorem': {
      assertOnlyKeys(
        value,
        ['rule', 'name', 'at', 'direction'],
        'theorem step',
      )
      const direction = str(value.direction, 'direction')
      if (direction !== 'forward' && direction !== 'reverse') {
        fail("direction must be 'forward'|'reverse'")
      }
      return {
        rule,
        name: str(value.name, 'name'),
        at: applicationFromJson(value.at, 'at'),
        direction,
      }
    }
    case 'vacuousIntro':
      assertOnlyKeys(value, ['rule', 'scope', 'sig'], 'vacuousIntro step')
      return {
        rule,
        scope: str(value.scope, 'scope'),
        sig: sigFromJson(value.sig, 'sig'),
      }
    case 'vacuousElim':
      assertOnlyKeys(value, ['rule', 'wireId'], 'vacuousElim step')
      return { rule, wireId: str(value.wireId, 'wireId') }
    case 'unfold':
      assertOnlyKeys(value, ['rule', 'nodeId'], 'unfold step')
      return { rule, nodeId: str(value.nodeId, 'nodeId') }
    case 'fold':
      assertOnlyKeys(
        value,
        ['rule', 'occurrence', 'args', 'defId'],
        'fold step',
      )
      return {
        rule,
        occurrence: selectionFromJson(value.occurrence, 'occurrence'),
        args: strArray(value.args, 'args'),
        defId: str(value.defId, 'defId'),
      }
    case 'cutWrap':
    case 'cutAbsorb':
    case 'parallelSplit':
    case 'endsDelete':
      assertOnlyKeys(value, ['rule', 'wire'], `${rule} step`)
      return { rule, wire: str(value.wire, 'wire') }
    case 'parallelFuse':
      assertOnlyKeys(value, ['rule', 'a', 'b'], 'parallelFuse step')
      return { rule, a: str(value.a, 'a'), b: str(value.b, 'b') }
    case 'endsSpawn': {
      assertOnlyKeys(value, ['rule', 'wire', 'sites'], 'endsSpawn step')
      if (!Array.isArray(value.sites)) return fail('endsSpawn sites must be an array')
      return {
        rule,
        wire: str(value.wire, 'wire'),
        sites: value.sites.map((site: unknown, index: number) => {
          if (typeof site !== 'object' || site === null) {
            return fail(`endsSpawn site ${index} must be an object`)
          }
          const record = site as Record<string, unknown>
          assertOnlyKeys(record, ['region', 'args'], `endsSpawn site ${index}`)
          return {
            region: str(record.region, `site ${index} region`),
            args: strArray(record.args, `site ${index} args`),
          }
        }),
      }
    }
    case 'arityShift':
      assertOnlyKeys(value, ['rule', 'wire', 'newArgSig'], 'arityShift step')
      return {
        rule,
        wire: str(value.wire, 'wire'),
        newArgSig: sigFromJson(value.newArgSig, 'newArgSig'),
      }
    case 'arityUnshift':
    case 'argDuplicate':
    case 'argContract':
    case 'argDrop':
    case 'applyFormal':
      assertOnlyKeys(value, ['rule', 'wire', 'position'], `${rule} step`)
      return {
        rule,
        wire: str(value.wire, 'wire'),
        position: nonNegativeSafeInteger(value.position, 'position'),
      }
    case 'argPermute': {
      assertOnlyKeys(value, ['rule', 'wire', 'permutation'], 'argPermute step')
      if (!Array.isArray(value.permutation)) {
        return fail('argPermute permutation must be an array')
      }
      return {
        rule,
        wire: str(value.wire, 'wire'),
        permutation: value.permutation.map((entry: unknown, index: number) =>
          nonNegativeSafeInteger(entry, `permutation[${index}]`)),
      }
    }
    case 'argExtend': {
      assertOnlyKeys(
        value,
        ['rule', 'wire', 'position', 'newArgSig', 'attachments'],
        'argExtend step',
      )
      if (!isRecord(value.attachments)) {
        return fail('argExtend attachments must be an object')
      }
      return {
        rule,
        wire: str(value.wire, 'wire'),
        position: nonNegativeSafeInteger(value.position, 'position'),
        newArgSig: sigFromJson(value.newArgSig, 'newArgSig'),
        attachments: Object.fromEntries(
          Object.entries(value.attachments).map(([node, wire]) =>
            [node, str(wire, `attachments['${node}']`)]),
        ),
      }
    }
    case 'abstractFormal':
      assertOnlyKeys(value, ['rule', 'ends', 'scope'], 'abstractFormal step')
      return {
        rule,
        ends: strArray(value.ends, 'ends'),
        scope: str(value.scope, 'scope'),
      }
    case 'identityLeaf':
      assertOnlyKeys(value, ['rule', 'wire'], 'identityLeaf step')
      return { rule, wire: str(value.wire, 'wire') }
    case 'identityAbstract':
      assertOnlyKeys(value, ['rule', 'nodes', 'scope'], 'identityAbstract step')
      return {
        rule,
        nodes: strArray(value.nodes, 'nodes'),
        scope: str(value.scope, 'scope'),
      }
    case 'refLeaf':
      assertOnlyKeys(value, ['rule', 'wire', 'defId'], 'refLeaf step')
      return {
        rule,
        wire: str(value.wire, 'wire'),
        defId: str(value.defId, 'defId'),
      }
    case 'refAbstract':
      assertOnlyKeys(value, ['rule', 'nodes', 'scope'], 'refAbstract step')
      return {
        rule,
        nodes: strArray(value.nodes, 'nodes'),
        scope: str(value.scope, 'scope'),
      }
    default:
      return fail(`unknown rule '${rule}'`)
  }
}

function placementToJson(placement: PlacementHint): unknown {
  return {
    introducedNode: placement.introducedNode,
    x: placement.x,
    y: placement.y,
  }
}

function finiteNumber(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    fail(`${what} must be a finite number`)
  }
  return value
}

function placementFromJson(value: unknown, what: string): PlacementHint {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['introducedNode', 'x', 'y'], what)
  return {
    introducedNode: nonNegativeSafeInteger(
      value.introducedNode,
      `${what}.introducedNode`,
    ),
    x: finiteNumber(value.x, `${what}.x`),
    y: finiteNumber(value.y, `${what}.y`),
  }
}

export function actionToJson(action: ProofAction): unknown {
  const allocation = action.allocation
  const hasAllocation = allocation !== undefined
    && (
      allocation.regions.length > 0
      || allocation.nodes.length > 0
      || allocation.wires.length > 0
    )
  return {
    label: action.label,
    steps: action.steps.map(stepToJson),
    placements: action.placements.map(placementToJson),
    ...(hasAllocation
      ? {
          allocation: {
            regions: [...allocation.regions],
            nodes: [...allocation.nodes],
            wires: [...allocation.wires],
          },
        }
      : {}),
  }
}

function allocationFromJson(
  value: unknown,
  what: string,
): ProofAllocation | undefined {
  if (value === undefined) return undefined
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['regions', 'nodes', 'wires'], what)
  const read = (
    field: 'regions' | 'nodes' | 'wires',
    singular: string,
  ): string[] => {
    const ids = strArray(value[field], `${what}.${field}`)
    const seen = new Set<string>()
    for (const id of ids) {
      if (id.length === 0) fail(`${what}.${field} ids must be non-empty strings`)
      if (seen.has(id)) fail(`duplicate ${singular} allocation id '${id}'`)
      seen.add(id)
    }
    return ids
  }
  const allocation: ProofAllocation = {
    regions: read('regions', 'region'),
    nodes: read('nodes', 'node'),
    wires: read('wires', 'wire'),
  }
  return allocation.regions.length > 0
    || allocation.nodes.length > 0
    || allocation.wires.length > 0
    ? allocation
    : undefined
}

export function actionFromJson(
  value: unknown,
  what = 'action',
): ProofAction {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['label', 'steps', 'placements', 'allocation'], what)
  if (!Array.isArray(value.steps)) fail(`${what}.steps must be an array`)
  if (!Array.isArray(value.placements)) {
    fail(`${what}.placements must be an array`)
  }
  const allocation = allocationFromJson(value.allocation, `${what}.allocation`)
  return {
    label: str(value.label, `${what}.label`),
    steps: value.steps.map(stepFromJson),
    placements: value.placements.map((placement, index) =>
      placementFromJson(placement, `${what}.placements[${index}]`)),
    ...(allocation === undefined ? {} : { allocation }),
  }
}

export function theoremToJson(theorem: Theorem): unknown {
  const backActions = theorem.backActions ?? []
  return {
    name: theorem.name,
    lhs: dwbToJson(theorem.lhs),
    rhs: dwbToJson(theorem.rhs),
    actions: theorem.actions.map(actionToJson),
    ...(backActions.length > 0
      ? { backActions: backActions.map(actionToJson) }
      : {}),
  }
}

export function theoremFromJson(value: unknown): Theorem {
  if (!isRecord(value)) fail('theorem must be an object')
  assertOnlyKeys(
    value,
    ['name', 'lhs', 'rhs', 'actions', 'backActions'],
    'theorem',
  )
  if (!Array.isArray(value.actions)) fail('theorem.actions must be an array')
  if (
    value.backActions !== undefined
    && !Array.isArray(value.backActions)
  ) {
    fail('theorem.backActions must be an array')
  }
  return {
    name: str(value.name, 'theorem.name'),
    lhs: dwbFromJson(value.lhs, 'theorem.lhs'),
    rhs: dwbFromJson(value.rhs, 'theorem.rhs'),
    actions: value.actions.map((action, index) =>
      actionFromJson(action, `theorem.actions[${index}]`)),
    ...(Array.isArray(value.backActions) && value.backActions.length > 0
      ? {
          backActions: value.backActions.map((action, index) =>
            actionFromJson(action, `theorem.backActions[${index}]`)),
        }
      : {}),
  }
}
