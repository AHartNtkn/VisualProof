import type { Endpoint } from '../diagram/diagram'
import { portKey } from '../diagram/diagram'
import { assertWellFormedTerm, type Term } from '../term/term'
import { deserializeTerm, serializeTerm } from '../term/serialize'
import type { PathSeg, ReductionStep } from '../term/reduce'
import type { ConversionCertificate } from '../term/certificate'
import {
  dwbFromJson,
  dwbToJson,
  parsePortKey,
  relSigFromJson,
  sigFromJson,
  sigToJson,
} from '../diagram/json'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type {
  IdentificationInput,
  PresentationInput,
  VacuityInstance,
} from '../rules/identity-rules'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type {
  WireJoinInput,
  WireSeverInput,
} from '../rules/wire-quantifier'
import {
  validateSlotCorrespondenceCarrier,
  type FreeVariableIdentityAction,
  type SlotCorrespondence,
} from '../rules/lambda'
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

function nonNegativeSafeIntegerArray(value: unknown, what: string): number[] {
  if (!Array.isArray(value)) fail(`${what} must be an array`)
  return value.map((item, index) =>
    nonNegativeSafeInteger(item, `${what}[${index}]`))
}

function pathFromJson(value: unknown, what: string): PathSeg[] {
  return strArray(value, what).map((segment, index) => {
    if (segment === 'body' || segment === 'fn' || segment === 'argument') {
      return segment
    }
    return fail(
      `${what}[${index}] is not a path segment (body|fn|argument): '${segment}'`,
    )
  })
}

function termFromJson(value: unknown, what: string): Term {
  try {
    return deserializeTerm(str(value, what))
  } catch (error) {
    return fail(`${what}: ${error instanceof Error ? error.message : String(error)}`)
  }
}

function reductionStepsToJson(steps: readonly ReductionStep[]): unknown {
  return steps.map((step) => ({ kind: step.kind, path: [...step.path] }))
}

function reductionStepsFromJson(value: unknown, what: string): ReductionStep[] {
  if (!Array.isArray(value)) fail(`${what} must be an array`)
  return value.map((step, index) => {
    if (!isRecord(step)) fail(`${what}[${index}] must be an object`)
    assertOnlyKeys(step, ['kind', 'path'], `${what}[${index}]`)
    const kind = str(step.kind, `${what}[${index}].kind`)
    if (kind !== 'beta' && kind !== 'eta') {
      fail(`${what}[${index}].kind must be beta|eta`)
    }
    return {
      kind,
      path: pathFromJson(step.path, `${what}[${index}].path`),
    }
  })
}

function conversionCertificateToJson(
  certificate: ConversionCertificate,
): unknown {
  return {
    leftSteps: reductionStepsToJson(certificate.leftSteps),
    rightSteps: reductionStepsToJson(certificate.rightSteps),
  }
}

function conversionCertificateFromJson(
  value: unknown,
  what: string,
): ConversionCertificate {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['leftSteps', 'rightSteps'], what)
  return {
    leftSteps: reductionStepsFromJson(value.leftSteps, `${what}.leftSteps`),
    rightSteps: reductionStepsFromJson(value.rightSteps, `${what}.rightSteps`),
  }
}

function slotCorrespondenceToJson(correspondence: SlotCorrespondence): unknown {
  return {
    commonArity: correspondence.commonArity,
    left: [...correspondence.left],
    right: [...correspondence.right],
  }
}

function slotCorrespondenceFromJson(
  value: unknown,
  what: string,
): SlotCorrespondence {
  if (!isRecord(value)) fail(`${what} must be an object`)
  assertOnlyKeys(value, ['commonArity', 'left', 'right'], what)
  const correspondence: SlotCorrespondence = {
    commonArity: nonNegativeSafeInteger(
      value.commonArity,
      `${what}.commonArity`,
    ),
    left: nonNegativeSafeIntegerArray(value.left, `${what}.left`),
    right: nonNegativeSafeIntegerArray(value.right, `${what}.right`),
  }
  try {
    validateSlotCorrespondenceCarrier(correspondence)
  } catch (error) {
    fail(`${what}: ${error instanceof Error ? error.message : String(error)}`)
  }
  return correspondence
}

function numericAttachmentsFromJson(
  value: unknown,
  what: string,
): Readonly<Record<number, string>> {
  if (!isRecord(value)) fail(`${what} must be an object`)
  const entries: Array<[number, string]> = []
  for (const [rawSlot, wire] of Object.entries(value)) {
    const slot = Number(rawSlot)
    if (
      !Number.isSafeInteger(slot)
      || slot < 0
      || String(slot) !== rawSlot
    ) {
      fail(`${what} key '${rawSlot}' must be a non-negative safe integer`)
    }
    entries.push([slot, str(wire, `${what}['${rawSlot}']`)])
  }
  return Object.fromEntries(entries)
}

function freeVariableIdentityActionFromJson(
  value: unknown,
): FreeVariableIdentityAction {
  if (!isRecord(value)) fail('lambdaFreeVariableIdentity action must be an object')
  const direction = str(value.direction, 'lambdaFreeVariableIdentity direction')
  if (direction === 'toIdentity') {
    assertOnlyKeys(
      value,
      ['direction', 'node'],
      'lambdaFreeVariableIdentity action',
    )
    return { direction, node: str(value.node, 'lambdaFreeVariableIdentity node') }
  }
  if (direction === 'toTerm') {
    assertOnlyKeys(
      value,
      ['direction', 'node', 'outputPort'],
      'lambdaFreeVariableIdentity action',
    )
    const outputPort = nonNegativeSafeInteger(
      value.outputPort,
      'lambdaFreeVariableIdentity outputPort',
    )
    if (outputPort !== 0 && outputPort !== 1) {
      fail('lambdaFreeVariableIdentity outputPort must be 0|1')
    }
    return {
      direction,
      node: str(value.node, 'lambdaFreeVariableIdentity node'),
      outputPort,
    }
  }
  return fail("lambdaFreeVariableIdentity direction must be 'toIdentity'|'toTerm'")
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

function wireSeverInputToJson(input: WireSeverInput): unknown {
  return {
    wire: input.wire,
    keep: input.keep.map(endpointToJson),
    ...(input.scope !== undefined ? { scope: input.scope } : {}),
  }
}

function wireSeverInputFromJson(value: unknown): WireSeverInput {
  if (!isRecord(value)) fail('wireSever input must be an object')
  assertOnlyKeys(value, ['wire', 'keep', 'scope'], 'wireSever input')
  if (!Array.isArray(value.keep)) {
    fail('wireSever input.keep must be an array')
  }
  return {
    wire: str(value.wire, 'wireSever input.wire'),
    keep: value.keep.map((endpoint, index) =>
      endpointFromJson(endpoint, `wireSever input.keep[${index}]`)),
    ...(value.scope !== undefined
      ? { scope: str(value.scope, 'wireSever input.scope') }
      : {}),
  }
}

function wireJoinInputToJson(input: WireJoinInput): unknown {
  return { a: input.a, b: input.b }
}

function wireJoinInputFromJson(value: unknown): WireJoinInput {
  if (!isRecord(value)) fail('wireJoin input must be an object')
  assertOnlyKeys(value, ['a', 'b'], 'wireJoin input')
  return {
    a: str(value.a, 'wireJoin input.a'),
    b: str(value.b, 'wireJoin input.b'),
  }
}

function vacuityInstanceToJson(instance: VacuityInstance): unknown {
  switch (instance.kind) {
    case 'point':
      return {
        kind: instance.kind,
        node: instance.node,
        region: instance.region,
        sig: sigToJson(instance.sig),
      }
    case 'stub':
      return {
        kind: instance.kind,
        base: instance.base,
        wire: instance.wire,
        end: instance.end,
        region: instance.region,
      }
    case 'pin':
      return {
        kind: instance.kind,
        wire: instance.wire,
        node: instance.node,
        region: instance.region,
      }
  }
}

function vacuityInstanceFromJson(value: unknown): VacuityInstance {
  if (!isRecord(value)) fail('vacuity instance must be an object')
  const kind = str(value.kind, 'vacuity instance kind')
  switch (kind) {
    case 'point':
      assertOnlyKeys(value, ['kind', 'node', 'region', 'sig'], 'vacuity point')
      return {
        kind,
        node: str(value.node, 'vacuity point node'),
        region: str(value.region, 'vacuity point region'),
        sig: sigFromJson(value.sig, 'vacuity point'),
      }
    case 'stub':
      assertOnlyKeys(value, ['kind', 'base', 'wire', 'end', 'region'], 'vacuity stub')
      return {
        kind,
        base: str(value.base, 'vacuity stub base'),
        wire: str(value.wire, 'vacuity stub wire'),
        end: str(value.end, 'vacuity stub end'),
        region: str(value.region, 'vacuity stub region'),
      }
    case 'pin':
      assertOnlyKeys(value, ['kind', 'wire', 'node', 'region'], 'vacuity pin')
      return {
        kind,
        wire: str(value.wire, 'vacuity pin wire'),
        node: str(value.node, 'vacuity pin node'),
        region: str(value.region, 'vacuity pin region'),
      }
    default:
      return fail(`unknown vacuity instance kind '${kind}'`)
  }
}

function presentationInputToJson(input: PresentationInput): unknown {
  return {
    region: input.region,
    removeNodes: [...input.removeNodes],
    addNodes: Object.fromEntries(
      Object.entries(input.addNodes).map(([id, ports]) => [id, [...ports]]),
    ),
  }
}

function presentationInputFromJson(value: unknown): PresentationInput {
  if (!isRecord(value)) fail('presentation input must be an object')
  assertOnlyKeys(value, ['region', 'removeNodes', 'addNodes'], 'presentation input')
  if (!isRecord(value.addNodes)) fail('presentation input.addNodes must be an object')
  return {
    region: str(value.region, 'presentation input.region'),
    removeNodes: strArray(value.removeNodes, 'presentation input.removeNodes'),
    addNodes: Object.fromEntries(
      Object.entries(value.addNodes).map(([id, ports]) =>
        [id, strArray(ports, `presentation input.addNodes['${id}']`)]),
    ),
  }
}

function identificationInputToJson(input: IdentificationInput): unknown {
  return input.kind === 'collapse'
    ? {
        kind: input.kind,
        node: input.node,
        survivor: input.survivor,
        absorbed: [...input.absorbed],
      }
    : {
        kind: input.kind,
        node: input.node,
        survivor: input.survivor,
        freshWire: input.freshWire,
        transfer: input.transfer.map(endpointToJson),
      }
}

function identificationInputFromJson(value: unknown): IdentificationInput {
  if (!isRecord(value)) fail('identification input must be an object')
  if (value.kind === 'collapse') {
    assertOnlyKeys(value, ['kind', 'node', 'survivor', 'absorbed'], 'identification input')
    return {
      kind: 'collapse',
      node: str(value.node, 'identification input.node'),
      survivor: str(value.survivor, 'identification input.survivor'),
      absorbed: strArray(value.absorbed, 'identification input.absorbed'),
    }
  }
  if (value.kind === 'expose') {
    assertOnlyKeys(
      value,
      ['kind', 'node', 'survivor', 'freshWire', 'transfer'],
      'identification input',
    )
    if (!Array.isArray(value.transfer)) fail('identification input.transfer must be an array')
    return {
      kind: 'expose',
      node: str(value.node, 'identification input.node'),
      survivor: str(value.survivor, 'identification input.survivor'),
      freshWire: str(value.freshWire, 'identification input.freshWire'),
      transfer: value.transfer.map((endpoint, index) =>
        endpointFromJson(endpoint, `identification input.transfer[${index}]`)),
    }
  }
  return fail("identification input.kind must be 'collapse'|'expose'")
}

/** Sorted by pattern id so the emitted JSON is insensitive to the matcher's
 *  internal insertion order; `idMapFromJson` rebuilds a `Map`, which is
 *  order-insensitive, so sorting here changes no round-tripped value. */
function idMapToJson(map: ReadonlyMap<string, string>): unknown {
  return [...map].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
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
      }
    case 'deiteration':
      return {
        rule: step.rule,
        sel: selectionToJson(step.sel),
        justifier: selectionToJson(step.justifier),
        certificate: occurrenceCertificateToJson(step.certificate),
      }
    case 'doubleCutIntro':
      return { rule: step.rule, sel: selectionToJson(step.sel) }
    case 'doubleCutElim':
      return { rule: step.rule, region: step.region }
    case 'lambdaTermSpawn':
      return {
        rule: step.rule,
        region: step.region,
        term: serializeTerm(step.term),
        freeArity: step.freeArity,
      }
    case 'lambdaConversion':
      return {
        rule: step.rule,
        node: step.node,
        term: serializeTerm(step.term),
        correspondence: slotCorrespondenceToJson(step.correspondence),
        certificate: conversionCertificateToJson(step.certificate),
        attachments: { ...step.attachments },
      }
    case 'lambdaFreeVariableIdentity':
      return { rule: step.rule, action: { ...step.action } }
    case 'lambdaFission':
      return { rule: step.rule, node: step.node, path: [...step.path] }
    case 'lambdaFusion':
      return { rule: step.rule, wire: step.wire }
    case 'lambdaCongruenceJoin':
      return {
        rule: step.rule,
        a: step.a,
        b: step.b,
        certificate: conversionCertificateToJson(step.certificate),
        correspondence: slotCorrespondenceToJson(step.correspondence),
      }
    case 'lambdaHeadStrip':
      return {
        rule: step.rule,
        a: step.a,
        b: step.b,
        correspondence: slotCorrespondenceToJson(step.correspondence),
      }
    case 'lambdaAnchoredWireSplit':
      return {
        rule: step.rule,
        wire: step.wire,
        witness: step.witness,
        endpoints: step.endpoints.map(endpointToJson),
        target: step.target,
      }
    case 'lambdaAnchoredWireContract':
      return {
        rule: step.rule,
        redundant: step.redundant,
        survivor: step.survivor,
        certificate: conversionCertificateToJson(step.certificate),
      }
    case 'theorem':
      return {
        rule: step.rule,
        name: step.name,
        at: applicationToJson(step.at),
        direction: step.direction,
      }
    case 'vacuity':
      return {
        rule: step.rule,
        direction: step.direction,
        instance: vacuityInstanceToJson(step.instance),
      }
    case 'presentation':
      return { rule: step.rule, input: presentationInputToJson(step.input) }
    case 'identification':
      return { rule: step.rule, input: identificationInputToJson(step.input) }
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
      assertOnlyKeys(value, ['rule', 'sel', 'target'], 'iteration step')
      return {
        rule,
        sel: selectionFromJson(value.sel, 'sel'),
        target: str(value.target, 'target'),
      }
    case 'deiteration':
      assertOnlyKeys(
        value,
        ['rule', 'sel', 'justifier', 'certificate'],
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
      }
    case 'doubleCutIntro':
      assertOnlyKeys(value, ['rule', 'sel'], 'doubleCutIntro step')
      return { rule, sel: selectionFromJson(value.sel, 'sel') }
    case 'doubleCutElim':
      assertOnlyKeys(value, ['rule', 'region'], 'doubleCutElim step')
      return { rule, region: str(value.region, 'region') }
    case 'lambdaTermSpawn': {
      assertOnlyKeys(
        value,
        ['rule', 'region', 'term', 'freeArity'],
        'lambdaTermSpawn step',
      )
      const term = termFromJson(value.term, 'term')
      const freeArity = nonNegativeSafeInteger(value.freeArity, 'freeArity')
      try {
        assertWellFormedTerm(term, freeArity)
      } catch (error) {
        fail(
          `lambdaTermSpawn term interface: `
          + `${error instanceof Error ? error.message : String(error)}`,
        )
      }
      return {
        rule,
        region: str(value.region, 'region'),
        term,
        freeArity,
      }
    }
    case 'lambdaConversion':
      assertOnlyKeys(
        value,
        ['rule', 'node', 'term', 'correspondence', 'certificate', 'attachments'],
        'lambdaConversion step',
      )
      return {
        rule,
        node: str(value.node, 'node'),
        term: termFromJson(value.term, 'term'),
        correspondence: slotCorrespondenceFromJson(
          value.correspondence,
          'correspondence',
        ),
        certificate: conversionCertificateFromJson(
          value.certificate,
          'certificate',
        ),
        attachments: numericAttachmentsFromJson(value.attachments, 'attachments'),
      }
    case 'lambdaFreeVariableIdentity':
      assertOnlyKeys(value, ['rule', 'action'], 'lambdaFreeVariableIdentity step')
      return {
        rule,
        action: freeVariableIdentityActionFromJson(value.action),
      }
    case 'lambdaFission':
      assertOnlyKeys(value, ['rule', 'node', 'path'], 'lambdaFission step')
      return {
        rule,
        node: str(value.node, 'node'),
        path: pathFromJson(value.path, 'path'),
      }
    case 'lambdaFusion':
      assertOnlyKeys(value, ['rule', 'wire'], 'lambdaFusion step')
      return { rule, wire: str(value.wire, 'wire') }
    case 'lambdaCongruenceJoin':
      assertOnlyKeys(
        value,
        ['rule', 'a', 'b', 'certificate', 'correspondence'],
        'lambdaCongruenceJoin step',
      )
      return {
        rule,
        a: str(value.a, 'a'),
        b: str(value.b, 'b'),
        certificate: conversionCertificateFromJson(value.certificate, 'certificate'),
        correspondence: slotCorrespondenceFromJson(value.correspondence, 'correspondence'),
      }
    case 'lambdaHeadStrip':
      assertOnlyKeys(
        value,
        ['rule', 'a', 'b', 'correspondence'],
        'lambdaHeadStrip step',
      )
      return {
        rule,
        a: str(value.a, 'a'),
        b: str(value.b, 'b'),
        correspondence: slotCorrespondenceFromJson(value.correspondence, 'correspondence'),
      }
    case 'lambdaAnchoredWireSplit':
      assertOnlyKeys(
        value,
        ['rule', 'wire', 'witness', 'endpoints', 'target'],
        'lambdaAnchoredWireSplit step',
      )
      if (!Array.isArray(value.endpoints)) {
        fail('lambdaAnchoredWireSplit endpoints must be an array')
      }
      return {
        rule,
        wire: str(value.wire, 'wire'),
        witness: str(value.witness, 'witness'),
        endpoints: value.endpoints.map((endpoint, index) =>
          endpointFromJson(endpoint, `endpoints[${index}]`)),
        target: str(value.target, 'target'),
      }
    case 'lambdaAnchoredWireContract':
      assertOnlyKeys(
        value,
        ['rule', 'redundant', 'survivor', 'certificate'],
        'lambdaAnchoredWireContract step',
      )
      return {
        rule,
        redundant: str(value.redundant, 'redundant'),
        survivor: str(value.survivor, 'survivor'),
        certificate: conversionCertificateFromJson(value.certificate, 'certificate'),
      }
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
    case 'vacuity': {
      assertOnlyKeys(value, ['rule', 'direction', 'instance'], 'vacuity step')
      const direction = str(value.direction, 'direction')
      if (direction !== 'insert' && direction !== 'delete') {
        fail("vacuity direction must be 'insert'|'delete'")
      }
      return { rule, direction, instance: vacuityInstanceFromJson(value.instance) }
    }
    case 'presentation':
      assertOnlyKeys(value, ['rule', 'input'], 'presentation step')
      return { rule, input: presentationInputFromJson(value.input) }
    case 'identification':
      assertOnlyKeys(value, ['rule', 'input'], 'identification step')
      return { rule, input: identificationInputFromJson(value.input) }
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
