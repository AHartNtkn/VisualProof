import type { Term } from '../term/term'
import { serializeTerm, deserializeTerm } from '../term/serialize'
import type { PathSeg, ReductionStep } from '../term/reduce'
import type { ConversionCertificate } from '../term/certificate'
import type { Endpoint, WireId } from '../diagram/diagram'
import { portKey } from '../diagram/diagram'
import { diagramToJson, diagramFromJson, parsePortKey } from '../diagram/json'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { AbstractionOccurrence } from '../rules/comprehension'
import type { ProofStep } from './step'
import type { PlacementHint, ProofAction, ProofAllocation } from './action'
import type { Theorem, TheoremApplication } from './theorem'
import {
  validatePortCorrespondenceCarrier,
  type PortCorrespondence,
} from '../rules/port-correspondence'

function fail(msg: string): never {
  throw new Error(`malformed proof JSON: ${msg}`)
}

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v)
}

function assertOnlyKeys(v: Record<string, unknown>, allowed: readonly string[], what: string): void {
  for (const k of Object.keys(v)) {
    if (!allowed.includes(k)) fail(`${what} has unknown field '${k}'`)
  }
}

function str(v: unknown, what: string): string {
  if (typeof v !== 'string') fail(`${what} must be a string`)
  return v
}

function strArray(v: unknown, what: string): string[] {
  if (!Array.isArray(v)) fail(`${what} must be an array`)
  return v.map((x, i) => str(x, `${what}[${i}]`))
}

function pathFromJson(v: unknown, what: string): PathSeg[] {
  return strArray(v, what).map((s, i) => {
    if (s === 'body' || s === 'fn' || s === 'arg') return s
    return fail(`${what}[${i}] is not a path segment (body|fn|arg): '${s}'`)
  })
}

function termFromJson(v: unknown, what: string): Term {
  try {
    return deserializeTerm(str(v, what))
  } catch (e) {
    return fail(`${what}: ${e instanceof Error ? e.message : String(e)}`)
  }
}

function selToJson(s: SubgraphSelection): unknown {
  return { region: s.region, regions: [...s.regions], nodes: [...s.nodes], wires: [...s.wires] }
}

function selFromJson(v: unknown, what: string): SubgraphSelection {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['region', 'regions', 'nodes', 'wires'], what)
  return {
    region: str(v.region, `${what}.region`),
    regions: strArray(v.regions, `${what}.regions`),
    nodes: strArray(v.nodes, `${what}.nodes`),
    wires: strArray(v.wires, `${what}.wires`),
  }
}

function endpointToJson(ep: Endpoint): unknown {
  return { node: ep.node, port: portKey(ep.port) }
}

function endpointFromJson(v: unknown, what: string): Endpoint {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['node', 'port'], what)
  return { node: str(v.node, `${what}.node`), port: parsePortKey(str(v.port, `${what}.port`)) }
}

export function dwbToJson(dwb: DiagramWithBoundary): unknown {
  return { diagram: diagramToJson(dwb.diagram), boundary: [...dwb.boundary] }
}

export function dwbFromJson(v: unknown, what = 'pattern'): DiagramWithBoundary {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['diagram', 'boundary'], what)
  try {
    return mkDiagramWithBoundary(diagramFromJson(v.diagram), strArray(v.boundary, `${what}.boundary`))
  } catch (e) {
    return fail(`${what}: ${e instanceof Error ? e.message : String(e)}`)
  }
}

function certToJson(c: ConversionCertificate): unknown {
  const steps = (xs: readonly ReductionStep[]) => xs.map((s) => ({ kind: s.kind, path: [...s.path] }))
  return { leftSteps: steps(c.leftSteps), rightSteps: steps(c.rightSteps) }
}

function certFromJson(v: unknown, what: string): ConversionCertificate {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['leftSteps', 'rightSteps'], what)
  const steps = (xs: unknown, w: string): ReductionStep[] => {
    if (!Array.isArray(xs)) fail(`${w} must be an array`)
    return xs.map((x, i) => {
      if (!isRecord(x)) fail(`${w}[${i}] must be an object`)
      assertOnlyKeys(x, ['kind', 'path'], `${w}[${i}]`)
      const kind = str(x.kind, `${w}[${i}].kind`)
      if (kind !== 'beta' && kind !== 'eta') fail(`${w}[${i}].kind must be beta|eta`)
      return { kind, path: pathFromJson(x.path, `${w}[${i}].path`) }
    })
  }
  return { leftSteps: steps(v.leftSteps, `${what}.leftSteps`), rightSteps: steps(v.rightSteps, `${what}.rightSteps`) }
}

function correspondenceToJson(correspondence: PortCorrespondence): unknown {
  return {
    commonArity: correspondence.commonArity,
    left: { ...correspondence.left },
    right: { ...correspondence.right },
  }
}

function correspondenceFromJson(v: unknown, what: string): PortCorrespondence {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['commonArity', 'left', 'right'], what)
  if (typeof v.commonArity !== 'number' || !Number.isSafeInteger(v.commonArity) || v.commonArity < 0) {
    fail(`${what}.commonArity must be a non-negative safe integer`)
  }
  const mapping = (side: unknown, label: string): Record<string, number> => {
    if (!isRecord(side)) fail(`${label} must be an object`)
    const entries: [string, number][] = []
    for (const [name, column] of Object.entries(side)) {
      if (typeof column !== 'number') fail(`${label}['${name}'] must be a number`)
      entries.push([name, column])
    }
    return Object.fromEntries(entries)
  }
  const correspondence: PortCorrespondence = {
    commonArity: v.commonArity,
    left: mapping(v.left, `${what}.left`),
    right: mapping(v.right, `${what}.right`),
  }
  try {
    validatePortCorrespondenceCarrier(correspondence)
  } catch (error) {
    fail(`${what}: ${error instanceof Error ? error.message : String(error)}`)
  }
  return correspondence
}

function idMapToJson(map: ReadonlyMap<string, string>): unknown {
  return [...map].sort(([left], [right]) => left.localeCompare(right))
}

function idMapFromJson(v: unknown, what: string): Map<string, string> {
  if (!Array.isArray(v)) fail(`${what} must be an array`)
  const result = new Map<string, string>()
  for (const [index, entry] of v.entries()) {
    if (!Array.isArray(entry) || entry.length !== 2) fail(`${what}[${index}] must be a [pattern, host] pair`)
    const pattern = str(entry[0], `${what}[${index}][0]`)
    const host = str(entry[1], `${what}[${index}][1]`)
    if (result.has(pattern)) fail(`${what} repeats pattern id '${pattern}'`)
    result.set(pattern, host)
  }
  return result
}

function occurrenceCertificateToJson(certificate: OccurrenceCertificate): unknown {
  return {
    region: certificate.region,
    regionMap: idMapToJson(certificate.regionMap),
    nodeMap: idMapToJson(certificate.nodeMap),
    wireMap: idMapToJson(certificate.wireMap),
    attachments: [...certificate.attachments],
    binderMap: idMapToJson(certificate.binderMap),
    termCertificates: [...certificate.termCertificates]
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([node, conversion]) => [node, certToJson(conversion)]),
  }
}

function occurrenceCertificateFromJson(v: unknown, what: string): OccurrenceCertificate {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, [
    'region', 'regionMap', 'nodeMap', 'wireMap', 'attachments', 'binderMap', 'termCertificates',
  ], what)
  if (!Array.isArray(v.termCertificates)) fail(`${what}.termCertificates must be an array`)
  const termCertificates = new Map<string, ConversionCertificate>()
  for (const [index, entry] of v.termCertificates.entries()) {
    if (!Array.isArray(entry) || entry.length !== 2) {
      fail(`${what}.termCertificates[${index}] must be a [node, certificate] pair`)
    }
    const node = str(entry[0], `${what}.termCertificates[${index}][0]`)
    if (termCertificates.has(node)) fail(`${what}.termCertificates repeats node '${node}'`)
    termCertificates.set(node, certFromJson(entry[1], `${what}.termCertificates[${index}][1]`))
  }
  return {
    region: str(v.region, `${what}.region`),
    regionMap: idMapFromJson(v.regionMap, `${what}.regionMap`),
    nodeMap: idMapFromJson(v.nodeMap, `${what}.nodeMap`),
    wireMap: idMapFromJson(v.wireMap, `${what}.wireMap`),
    attachments: strArray(v.attachments, `${what}.attachments`),
    binderMap: idMapFromJson(v.binderMap, `${what}.binderMap`),
    termCertificates,
  }
}

function occToJson(o: AbstractionOccurrence): unknown {
  return { sel: selToJson(o.sel), args: [...o.args] }
}

function occFromJson(v: unknown, what: string): AbstractionOccurrence {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['sel', 'args'], what)
  return { sel: selFromJson(v.sel, `${what}.sel`), args: strArray(v.args, `${what}.args`) }
}

function appToJson(a: TheoremApplication): unknown {
  return { sel: selToJson(a.sel), args: [...a.args] }
}

function appFromJson(v: unknown, what: string): TheoremApplication {
  if (!isRecord(v)) fail(`${what} must be an object`)
  assertOnlyKeys(v, ['sel', 'args'], what)
  return { sel: selFromJson(v.sel, `${what}.sel`), args: strArray(v.args, `${what}.args`) }
}

export function stepToJson(s: ProofStep): unknown {
  switch (s.rule) {
    case 'openTermSpawn':
      return { rule: s.rule, region: s.region, term: serializeTerm(s.term) }
    case 'relationSpawn':
      return { rule: s.rule, region: s.region, defId: s.defId, arity: s.arity }
    case 'boundRelationSpawn':
      return { rule: s.rule, region: s.region, binder: s.binder, arity: s.arity }
    case 'wireJoin':
      return { rule: s.rule, a: s.a, b: s.b }
    case 'erasure':
      return { rule: s.rule, sel: selToJson(s.sel) }
    case 'wireSever':
      return { rule: s.rule, wire: s.wire, keep: s.keep.map(endpointToJson) }
    case 'iteration':
      return { rule: s.rule, sel: selToJson(s.sel), target: s.target }
    case 'deiteration':
      return {
        rule: s.rule,
        sel: selToJson(s.sel),
        justifier: selToJson(s.justifier),
        certificate: occurrenceCertificateToJson(s.certificate),
      }
    case 'doubleCutIntro':
      return { rule: s.rule, sel: selToJson(s.sel) }
    case 'doubleCutElim':
      return { rule: s.rule, region: s.region }
    case 'conversion':
      return { rule: s.rule, node: s.node, term: serializeTerm(s.term), certificate: certToJson(s.certificate), correspondence: correspondenceToJson(s.correspondence), attachments: { ...s.attachments } }
    case 'congruenceJoin':
      return { rule: s.rule, a: s.a, b: s.b, certificate: certToJson(s.certificate), correspondence: correspondenceToJson(s.correspondence) }
    case 'anchoredWireSplit':
      return { rule: s.rule, wire: s.wire, witness: s.witness, endpoints: s.endpoints.map(endpointToJson), target: s.target }
    case 'anchoredWireContract':
      return { rule: s.rule, redundant: s.redundant, survivor: s.survivor, certificate: certToJson(s.certificate) }
    case 'headStrip':
      return { rule: s.rule, a: s.a, b: s.b, correspondence: correspondenceToJson(s.correspondence) }
    case 'closedTermIntro':
      return { rule: s.rule, region: s.region, term: serializeTerm(s.term) }
    case 'fusion':
      return { rule: s.rule, wire: s.wire }
    case 'fission':
      return { rule: s.rule, node: s.node, path: [...s.path] }
    case 'comprehensionInstantiate':
      return {
        rule: s.rule,
        bubble: s.bubble,
        comp: dwbToJson(s.comp),
        attachments: [...s.attachments],
        binders: s.binders.map(([pattern, host]) => [pattern, host]),
      }
    case 'comprehensionAbstract':
      return { rule: s.rule, wrap: selToJson(s.wrap), comp: dwbToJson(s.comp), occurrences: s.occurrences.map(occToJson) }
    case 'theorem':
      return { rule: s.rule, name: s.name, at: appToJson(s.at), direction: s.direction }
    case 'vacuousIntro':
      return { rule: s.rule, sel: selToJson(s.sel), arity: s.arity }
    case 'vacuousElim':
      return { rule: s.rule, region: s.region }
    case 'relUnfold':
      return { rule: s.rule, node: s.node }
    case 'relFold':
      return { rule: s.rule, sel: selToJson(s.sel), defId: s.defId, args: [...s.args] }
  }
}

export function stepFromJson(j: unknown): ProofStep {
  if (!isRecord(j)) fail('step must be an object')
  const rule = str(j.rule, 'step.rule')
  switch (rule) {
    case 'openTermSpawn':
      assertOnlyKeys(j, ['rule', 'region', 'term'], 'openTermSpawn step')
      return { rule, region: str(j.region, 'region'), term: termFromJson(j.term, 'term') }
    case 'relationSpawn': {
      assertOnlyKeys(j, ['rule', 'region', 'defId', 'arity'], 'relationSpawn step')
      if (typeof j.arity !== 'number' || !Number.isSafeInteger(j.arity) || j.arity < 0) fail('arity must be a non-negative safe integer')
      return { rule, region: str(j.region, 'region'), defId: str(j.defId, 'defId'), arity: j.arity }
    }
    case 'boundRelationSpawn':
      assertOnlyKeys(j, ['rule', 'region', 'binder', 'arity'], 'boundRelationSpawn step')
      if (typeof j.arity !== 'number' || !Number.isSafeInteger(j.arity) || j.arity < 0) fail('arity must be a non-negative safe integer')
      return { rule, region: str(j.region, 'region'), binder: str(j.binder, 'binder'), arity: j.arity }
    case 'wireJoin':
      assertOnlyKeys(j, ['rule', 'a', 'b'], 'wireJoin step')
      return { rule, a: str(j.a, 'a'), b: str(j.b, 'b') }
    case 'erasure':
      assertOnlyKeys(j, ['rule', 'sel'], 'erasure step')
      return { rule, sel: selFromJson(j.sel, 'sel') }
    case 'wireSever': {
      assertOnlyKeys(j, ['rule', 'wire', 'keep'], 'wireSever step')
      if (!Array.isArray(j.keep)) fail('keep must be an array')
      return { rule, wire: str(j.wire, 'wire'), keep: j.keep.map((k, i) => endpointFromJson(k, `keep[${i}]`)) }
    }
    case 'iteration':
      assertOnlyKeys(j, ['rule', 'sel', 'target'], 'iteration step')
      return { rule, sel: selFromJson(j.sel, 'sel'), target: str(j.target, 'target') }
    case 'deiteration': {
      assertOnlyKeys(j, ['rule', 'sel', 'justifier', 'certificate'], 'deiteration step')
      return {
        rule,
        sel: selFromJson(j.sel, 'sel'),
        justifier: selFromJson(j.justifier, 'justifier'),
        certificate: occurrenceCertificateFromJson(j.certificate, 'certificate'),
      }
    }
    case 'doubleCutIntro':
      assertOnlyKeys(j, ['rule', 'sel'], 'doubleCutIntro step')
      return { rule, sel: selFromJson(j.sel, 'sel') }
    case 'doubleCutElim':
      assertOnlyKeys(j, ['rule', 'region'], 'doubleCutElim step')
      return { rule, region: str(j.region, 'region') }
    case 'conversion': {
      assertOnlyKeys(j, ['rule', 'node', 'term', 'certificate', 'correspondence', 'attachments'], 'conversion step')
      if (!isRecord(j.attachments)) fail('attachments must be an object')
      const attachments = Object.fromEntries(
        Object.entries(j.attachments).map(([k, v]) => [k, str(v, `attachments['${k}']`)]),
      ) as Record<string, WireId>
      return { rule, node: str(j.node, 'node'), term: termFromJson(j.term, 'term'), certificate: certFromJson(j.certificate, 'certificate'), correspondence: correspondenceFromJson(j.correspondence, 'correspondence'), attachments }
    }
    case 'congruenceJoin':
      assertOnlyKeys(j, ['rule', 'a', 'b', 'certificate', 'correspondence'], 'congruenceJoin step')
      return { rule, a: str(j.a, 'a'), b: str(j.b, 'b'), certificate: certFromJson(j.certificate, 'certificate'), correspondence: correspondenceFromJson(j.correspondence, 'correspondence') }
    case 'anchoredWireSplit': {
      assertOnlyKeys(j, ['rule', 'wire', 'witness', 'endpoints', 'target'], 'anchoredWireSplit step')
      if (!Array.isArray(j.endpoints)) fail('endpoints must be an array')
      return {
        rule,
        wire: str(j.wire, 'wire'),
        witness: str(j.witness, 'witness'),
        endpoints: j.endpoints.map((endpoint, index) => endpointFromJson(endpoint, `endpoints[${index}]`)),
        target: str(j.target, 'target'),
      }
    }
    case 'anchoredWireContract':
      assertOnlyKeys(j, ['rule', 'redundant', 'survivor', 'certificate'], 'anchoredWireContract step')
      return {
        rule,
        redundant: str(j.redundant, 'redundant'),
        survivor: str(j.survivor, 'survivor'),
        certificate: certFromJson(j.certificate, 'certificate'),
      }
    case 'headStrip':
      assertOnlyKeys(j, ['rule', 'a', 'b', 'correspondence'], 'headStrip step')
      return { rule, a: str(j.a, 'a'), b: str(j.b, 'b'), correspondence: correspondenceFromJson(j.correspondence, 'correspondence') }
    case 'closedTermIntro':
      assertOnlyKeys(j, ['rule', 'region', 'term'], 'closedTermIntro step')
      return { rule, region: str(j.region, 'region'), term: termFromJson(j.term, 'term') }
    case 'fusion':
      assertOnlyKeys(j, ['rule', 'wire'], 'fusion step')
      return { rule, wire: str(j.wire, 'wire') }
    case 'fission':
      assertOnlyKeys(j, ['rule', 'node', 'path'], 'fission step')
      return { rule, node: str(j.node, 'node'), path: pathFromJson(j.path, 'path') }
    case 'comprehensionInstantiate': {
      assertOnlyKeys(j, ['rule', 'bubble', 'comp', 'attachments', 'binders'], 'comprehensionInstantiate step')
      if (!Array.isArray(j.binders)) fail('binders must be an array')
      const binders: Array<readonly [string, string]> = []
      const patterns = new Set<string>()
      const targets = new Set<string>()
      for (const [index, entry] of j.binders.entries()) {
        if (!Array.isArray(entry) || entry.length !== 2) {
          fail(`binders[${index}] must be a [pattern, host] pair`)
        }
        const pattern = str(entry[0], `binders[${index}][0]`)
        const host = str(entry[1], `binders[${index}][1]`)
        if (patterns.has(pattern)) fail(`binders repeats pattern id '${pattern}'`)
        if (targets.has(host)) fail(`binders repeats host target '${host}'`)
        patterns.add(pattern)
        targets.add(host)
        binders.push([pattern, host])
      }
      return { rule, bubble: str(j.bubble, 'bubble'), comp: dwbFromJson(j.comp, 'comp'), attachments: strArray(j.attachments, 'attachments'), binders }
    }
    case 'comprehensionAbstract': {
      assertOnlyKeys(j, ['rule', 'wrap', 'comp', 'occurrences'], 'comprehensionAbstract step')
      if (!Array.isArray(j.occurrences)) fail('occurrences must be an array')
      return { rule, wrap: selFromJson(j.wrap, 'wrap'), comp: dwbFromJson(j.comp, 'comp'), occurrences: j.occurrences.map((o, i) => occFromJson(o, `occurrences[${i}]`)) }
    }
    case 'theorem': {
      assertOnlyKeys(j, ['rule', 'name', 'at', 'direction'], 'theorem step')
      const direction = str(j.direction, 'direction')
      if (direction !== 'forward' && direction !== 'reverse') fail("direction must be 'forward'|'reverse'")
      return { rule, name: str(j.name, 'name'), at: appFromJson(j.at, 'at'), direction }
    }
    case 'vacuousIntro': {
      assertOnlyKeys(j, ['rule', 'sel', 'arity'], 'vacuousIntro step')
      if (typeof j.arity !== 'number' || !Number.isSafeInteger(j.arity) || j.arity < 0) fail('arity must be a non-negative safe integer')
      return { rule, sel: selFromJson(j.sel, 'sel'), arity: j.arity }
    }
    case 'vacuousElim':
      assertOnlyKeys(j, ['rule', 'region'], 'vacuousElim step')
      return { rule, region: str(j.region, 'region') }
    case 'relUnfold':
      assertOnlyKeys(j, ['rule', 'node'], 'relUnfold step')
      return { rule, node: str(j.node, 'node') }
    case 'relFold':
      assertOnlyKeys(j, ['rule', 'sel', 'defId', 'args'], 'relFold step')
      return { rule, sel: selFromJson(j.sel, 'sel'), defId: str(j.defId, 'defId'), args: strArray(j.args, 'args') }
    default:
      return fail(`unknown rule '${rule}'`)
  }
}

function placementToJson(placement: PlacementHint): unknown {
  return { introducedNode: placement.introducedNode, x: placement.x, y: placement.y }
}

function finiteNumber(v: unknown, what: string): number {
  if (typeof v !== 'number' || !Number.isFinite(v)) fail(`${what} must be a finite number`)
  return v
}

function placementFromJson(j: unknown, what: string): PlacementHint {
  if (!isRecord(j)) fail(`${what} must be an object`)
  assertOnlyKeys(j, ['introducedNode', 'x', 'y'], what)
  const introducedNode = finiteNumber(j.introducedNode, `${what}.introducedNode`)
  if (!Number.isInteger(introducedNode) || introducedNode < 0) {
    fail(`${what}.introducedNode must be a non-negative integer`)
  }
  return {
    introducedNode,
    x: finiteNumber(j.x, `${what}.x`),
    y: finiteNumber(j.y, `${what}.y`),
  }
}

export function actionToJson(action: ProofAction): unknown {
  const allocation = action.allocation
  const hasAllocation = allocation !== undefined
    && (allocation.regions.length > 0 || allocation.nodes.length > 0 || allocation.wires.length > 0)
  return {
    label: action.label,
    steps: action.steps.map(stepToJson),
    placements: action.placements.map(placementToJson),
    ...(hasAllocation ? { allocation: {
      regions: [...allocation.regions],
      nodes: [...allocation.nodes],
      wires: [...allocation.wires],
    } } : {}),
  }
}

function allocationFromJson(value: unknown, what: string): ProofAllocation | undefined {
  if (value === undefined) return undefined
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['regions', 'nodes', 'wires'], what)
  const read = (field: 'regions' | 'nodes' | 'wires', singular: string): string[] => {
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
  return allocation.regions.length > 0 || allocation.nodes.length > 0 || allocation.wires.length > 0
    ? allocation
    : undefined
}

export function actionFromJson(j: unknown, what = 'action'): ProofAction {
  if (!isRecord(j)) fail(`${what} must be an object`)
  assertOnlyKeys(j, ['label', 'steps', 'placements', 'allocation'], what)
  if (!Array.isArray(j.steps)) fail(`${what}.steps must be an array`)
  if (!Array.isArray(j.placements)) fail(`${what}.placements must be an array`)
  const allocation = allocationFromJson(j.allocation, `${what}.allocation`)
  return {
    label: str(j.label, `${what}.label`),
    steps: j.steps.map(stepFromJson),
    placements: j.placements.map((placement, index) => placementFromJson(placement, `${what}.placements[${index}]`)),
    ...(allocation === undefined ? {} : { allocation }),
  }
}

export function theoremToJson(t: Theorem): unknown {
  const backActions = t.backActions ?? []
  return {
    name: t.name, lhs: dwbToJson(t.lhs), rhs: dwbToJson(t.rhs),
    actions: t.actions.map(actionToJson),
    ...(backActions.length > 0 ? { backActions: backActions.map(actionToJson) } : {}),
  }
}

export function theoremFromJson(j: unknown): Theorem {
  if (!isRecord(j)) fail('theorem must be an object')
  assertOnlyKeys(j, ['name', 'lhs', 'rhs', 'actions', 'backActions'], 'theorem')
  if (!Array.isArray(j.actions)) fail('theorem.actions must be an array')
  if (j.backActions !== undefined && !Array.isArray(j.backActions)) fail('theorem.backActions must be an array')
  return {
    name: str(j.name, 'theorem.name'),
    lhs: dwbFromJson(j.lhs, 'theorem.lhs'),
    rhs: dwbFromJson(j.rhs, 'theorem.rhs'),
    actions: j.actions.map((action, index) => actionFromJson(action, `theorem.actions[${index}]`)),
    ...(Array.isArray(j.backActions) && j.backActions.length > 0
      ? { backActions: j.backActions.map((action, index) => actionFromJson(action, `theorem.backActions[${index}]`)) }
      : {}),
  }
}
