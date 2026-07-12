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
import type { AbstractionOccurrence } from '../rules/comprehension'
import type { ProofStep } from './step'
import type { Theorem, TheoremApplication } from './theorem'

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
      return { rule: s.rule, region: s.region, binder: s.binder }
    case 'wireJoin':
      return { rule: s.rule, a: s.a, b: s.b }
    case 'erasure':
      return { rule: s.rule, sel: selToJson(s.sel) }
    case 'wireSever':
      return { rule: s.rule, wire: s.wire, keep: s.keep.map(endpointToJson) }
    case 'iteration':
      return { rule: s.rule, sel: selToJson(s.sel), target: s.target }
    case 'deiteration':
      return { rule: s.rule, sel: selToJson(s.sel), fuel: s.fuel }
    case 'doubleCutIntro':
      return { rule: s.rule, sel: selToJson(s.sel) }
    case 'doubleCutElim':
      return { rule: s.rule, region: s.region }
    case 'conversion':
      return { rule: s.rule, node: s.node, term: serializeTerm(s.term), certificate: certToJson(s.certificate), attachments: { ...s.attachments } }
    case 'congruenceJoin':
      return { rule: s.rule, a: s.a, b: s.b, certificate: certToJson(s.certificate) }
    case 'anchoredWireSplit':
      return { rule: s.rule, wire: s.wire, witness: s.witness, endpoints: s.endpoints.map(endpointToJson), target: s.target }
    case 'anchoredWireContract':
      return { rule: s.rule, redundant: s.redundant, survivor: s.survivor, certificate: certToJson(s.certificate) }
    case 'headStrip':
      return { rule: s.rule, a: s.a, b: s.b }
    case 'closedTermIntro':
      return { rule: s.rule, region: s.region, term: serializeTerm(s.term) }
    case 'fusion':
      return { rule: s.rule, wire: s.wire }
    case 'fission':
      return { rule: s.rule, node: s.node, path: [...s.path] }
    case 'comprehensionInstantiate':
      return { rule: s.rule, bubble: s.bubble, comp: dwbToJson(s.comp), attachments: [...s.attachments], binders: { ...s.binders } }
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
      assertOnlyKeys(j, ['rule', 'region', 'binder'], 'boundRelationSpawn step')
      return { rule, region: str(j.region, 'region'), binder: str(j.binder, 'binder') }
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
      assertOnlyKeys(j, ['rule', 'sel', 'fuel'], 'deiteration step')
      if (typeof j.fuel !== 'number' || !Number.isInteger(j.fuel) || j.fuel <= 0) fail('fuel must be a positive integer')
      return { rule, sel: selFromJson(j.sel, 'sel'), fuel: j.fuel }
    }
    case 'doubleCutIntro':
      assertOnlyKeys(j, ['rule', 'sel'], 'doubleCutIntro step')
      return { rule, sel: selFromJson(j.sel, 'sel') }
    case 'doubleCutElim':
      assertOnlyKeys(j, ['rule', 'region'], 'doubleCutElim step')
      return { rule, region: str(j.region, 'region') }
    case 'conversion': {
      assertOnlyKeys(j, ['rule', 'node', 'term', 'certificate', 'attachments'], 'conversion step')
      if (!isRecord(j.attachments)) fail('attachments must be an object')
      const attachments: Record<string, WireId> = {}
      for (const [k, v] of Object.entries(j.attachments)) attachments[k] = str(v, `attachments['${k}']`)
      return { rule, node: str(j.node, 'node'), term: termFromJson(j.term, 'term'), certificate: certFromJson(j.certificate, 'certificate'), attachments }
    }
    case 'congruenceJoin':
      assertOnlyKeys(j, ['rule', 'a', 'b', 'certificate'], 'congruenceJoin step')
      return { rule, a: str(j.a, 'a'), b: str(j.b, 'b'), certificate: certFromJson(j.certificate, 'certificate') }
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
      assertOnlyKeys(j, ['rule', 'a', 'b'], 'headStrip step')
      return { rule, a: str(j.a, 'a'), b: str(j.b, 'b') }
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
      if (!isRecord(j.binders)) fail('binders must be an object')
      const binders: Record<string, string> = {}
      for (const [k, v] of Object.entries(j.binders)) binders[k] = str(v, `binders['${k}']`)
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

export function theoremToJson(t: Theorem): unknown {
  const backSteps = t.backSteps ?? []
  return {
    name: t.name, lhs: dwbToJson(t.lhs), rhs: dwbToJson(t.rhs),
    steps: t.steps.map(stepToJson),
    // dual-replay form: backward-oriented steps, replayed from the rhs.
    // Omitted when empty so classic all-forward files stay byte-identical.
    ...(backSteps.length > 0 ? { backSteps: backSteps.map(stepToJson) } : {}),
  }
}

export function theoremFromJson(j: unknown): Theorem {
  if (!isRecord(j)) fail('theorem must be an object')
  assertOnlyKeys(j, ['name', 'lhs', 'rhs', 'steps', 'backSteps'], 'theorem')
  if (!Array.isArray(j.steps)) fail('theorem.steps must be an array')
  if (j.backSteps !== undefined && !Array.isArray(j.backSteps)) fail('theorem.backSteps must be an array')
  return {
    name: str(j.name, 'theorem.name'),
    lhs: dwbFromJson(j.lhs, 'theorem.lhs'),
    rhs: dwbFromJson(j.rhs, 'theorem.rhs'),
    steps: j.steps.map((s) => stepFromJson(s)),
    ...(Array.isArray(j.backSteps) && j.backSteps.length > 0 ? { backSteps: j.backSteps.map((s) => stepFromJson(s)) } : {}),
  }
}
