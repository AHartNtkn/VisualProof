import type { Term } from '../term/term'
import type { PathSeg } from '../term/reduce'
import type { ConversionCertificate, NormalSeparationCertificate } from '../term/certificate'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram/diagram'
import type { IdReservation } from '../diagram/subgraph/freshId'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { PortCorrespondence } from '../rules/port-correspondence'
import { applyWireJoin } from '../rules/wire-join'
import { applyOpenTermSpawn, applyRelationSpawn, applyBoundRelationSpawn } from '../rules/spawn'
import { applyErasure, applyWireSever } from '../rules/erasure'
import { applyIteration, applyDeiteration } from '../rules/iteration'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../rules/doublecut'
import { applyInconsistentCutElim } from '../rules/inconsistent-cut'
import { applyConversionByCertificate } from '../rules/conversion'
import { applyCongruenceJoin } from '../rules/congruence'
import { anchorAvailability, applyAnchoredWireSplit, applyAnchoredWireContract } from '../rules/anchored-wire'
import { applyHeadStrip } from '../rules/headstrip'
import { applyClosedTermIntro } from '../rules/intro'
import { applyFusion, applyFission } from '../rules/fusion'
import { applyComprehensionInstantiate, applyComprehensionAbstract } from '../rules/comprehension'
import type { AbstractionOccurrence, ComprehensionBinderPair } from '../rules/comprehension'
import { applyVacuousBubbleIntro, applyVacuousBubbleElim } from '../rules/vacuous'
import { applyRelUnfold, applyRelFold } from '../rules/reldef'
import type { TheoremApplication } from './theorem'
import { applyTheorem } from './theorem'
import { ProofError } from './error'
import type { ProofContext } from './context'
import { assertProofContext } from './context'

/**
 * One serializable rule application. Replay carries no trust: applyStep calls
 * the real appliers, each enforcing its own gate. Conversion replays by
 * certificates. Replay is entirely fuel-free and never reruns proof search.
 */
export type ProofStep =
  | { readonly rule: 'openTermSpawn'; readonly region: RegionId; readonly term: Term; readonly freePorts: readonly string[] }
  | { readonly rule: 'relationSpawn'; readonly region: RegionId; readonly defId: string; readonly arity: number }
  | { readonly rule: 'boundRelationSpawn'; readonly region: RegionId; readonly binder: RegionId; readonly arity: number }
  | { readonly rule: 'wireJoin'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'erasure'; readonly sel: SubgraphSelection }
  | { readonly rule: 'wireSever'; readonly wire: WireId; readonly keep: readonly Endpoint[] }
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly justifier: SubgraphSelection; readonly certificate: OccurrenceCertificate }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'inconsistentCutElim'; readonly region: RegionId; readonly first: NodeId; readonly second: NodeId; readonly certificate: NormalSeparationCertificate }
  | { readonly rule: 'conversion'; readonly node: NodeId; readonly term: Term; readonly certificate: ConversionCertificate; readonly correspondence: PortCorrespondence; readonly attachments: Readonly<Record<string, WireId>> }
  | { readonly rule: 'congruenceJoin'; readonly a: NodeId; readonly b: NodeId; readonly certificate: ConversionCertificate; readonly correspondence: PortCorrespondence }
  | { readonly rule: 'anchoredWireSplit'; readonly wire: WireId; readonly witness: NodeId; readonly endpoints: readonly Endpoint[]; readonly target: RegionId }
  | { readonly rule: 'anchoredWireContract'; readonly redundant: NodeId; readonly survivor: NodeId; readonly certificate: ConversionCertificate }
  | { readonly rule: 'headStrip'; readonly a: NodeId; readonly b: NodeId; readonly correspondence: PortCorrespondence }
  | { readonly rule: 'closedTermIntro'; readonly region: RegionId; readonly term: Term }
  | { readonly rule: 'fusion'; readonly wire: WireId }
  | { readonly rule: 'fission'; readonly node: NodeId; readonly path: readonly PathSeg[] }
  | { readonly rule: 'comprehensionInstantiate'; readonly bubble: RegionId; readonly comp: DiagramWithBoundary; readonly attachments: readonly WireId[]; readonly binders: readonly ComprehensionBinderPair[] }
  | { readonly rule: 'comprehensionAbstract'; readonly wrap: SubgraphSelection; readonly comp: DiagramWithBoundary; readonly occurrences: readonly AbstractionOccurrence[] }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }
  | { readonly rule: 'vacuousIntro'; readonly sel: SubgraphSelection; readonly arity: number }
  | { readonly rule: 'vacuousElim'; readonly region: RegionId }
  | { readonly rule: 'relUnfold'; readonly node: NodeId }
  | { readonly rule: 'relFold'; readonly sel: SubgraphSelection; readonly defId: string; readonly args: readonly WireId[] }

/** Logical transport of source wire identities through one proof step.
 * Unlike graph provenance, distinct source identities may intentionally
 * coalesce. An absent image means the identity cannot remain on an open
 * boundary after this step. */
export type WireInterfaceTransport = {
  readonly image: (wire: WireId) => WireId | undefined
}

/** Injective graph-identity provenance through one proof step.
 * A source wire has an image exactly when that same identity survives as a
 * root-scoped result wire. Unlike the logical interface, provenance never
 * coalesces distinct source identities. */
export type WireProvenance = {
  readonly image: (wire: WireId) => WireId | undefined
}

/** Authoritative result of executing one serialized proof step. */
export type StepReceipt = {
  readonly result: Diagram
  readonly provenance: WireProvenance
  readonly interface: WireInterfaceTransport
}

/** Ordered boundary transport. Positions and repeated aliases are preserved. */
export function transportBoundary(
  transport: WireInterfaceTransport,
  boundary: readonly WireId[],
): readonly WireId[] | undefined {
  const mapped: WireId[] = []
  for (const wire of boundary) {
    const image = transport.image(wire)
    if (image === undefined) return undefined
    mapped.push(image)
  }
  return mapped
}

function rootFilteredInterface(
  target: Diagram,
  candidate: (wire: WireId) => WireId | undefined,
): WireInterfaceTransport {
  return {
    image(wire) {
      const mapped = candidate(wire)
      if (mapped === undefined) return undefined
      const targetWire = target.wires[mapped]
      return targetWire !== undefined && targetWire.scope === target.root ? mapped : undefined
    },
  }
}

function rootFilteredProvenance(
  target: Diagram,
  candidate: (wire: WireId) => WireId | undefined,
): WireProvenance {
  return {
    image(wire) {
      const mapped = candidate(wire)
      if (mapped === undefined) return undefined
      const targetWire = target.wires[mapped]
      return targetWire !== undefined && targetWire.scope === target.root ? mapped : undefined
    },
  }
}

/**
 * Apply one step. `orientation` is the reasoning direction: 'forward' (the
 * default — replay and forward proving) keeps every gate as stated;
 * 'backward' (acting on a GOAL) flips exactly the polarity-tied gates
 * (erasure, atomic spawning, wire joining, theorem citation) — the calculus's cut symmetry.
 * Execution is IDENTICAL either way: one applier per rule, no mirrors.
 */
function applyStepRaw(
  d: Diagram,
  step: ProofStep,
  ctx: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  switch (step.rule) {
    case 'openTermSpawn': return applyOpenTermSpawn(d, step.region, step.term, step.freePorts, orientation, reservation)
    case 'relationSpawn': return applyRelationSpawn(d, step.region, step.defId, step.arity, ctx.relations, orientation, reservation)
    case 'boundRelationSpawn': return applyBoundRelationSpawn(d, step.region, step.binder, step.arity, orientation, reservation)
    case 'wireJoin': return applyWireJoin(d, step.a, step.b, orientation)
    case 'erasure': return applyErasure(d, step.sel, orientation)
    case 'wireSever': return applyWireSever(d, step.wire, step.keep, orientation, reservation)
    case 'iteration': return applyIteration(d, step.sel, step.target, reservation)
    case 'deiteration': return applyDeiteration(d, step.sel, step.justifier, step.certificate)
    case 'doubleCutIntro': return applyDoubleCutIntro(d, step.sel, reservation)
    case 'doubleCutElim': return applyDoubleCutElim(d, step.region)
    case 'inconsistentCutElim': return applyInconsistentCutElim(d, step.region, step.first, step.second, step.certificate)
    case 'conversion': return applyConversionByCertificate(d, step.node, step.term, step.certificate, step.correspondence, step.attachments, reservation)
    case 'congruenceJoin': return applyCongruenceJoin(d, step.a, step.b, step.certificate, step.correspondence)
    case 'anchoredWireSplit': return applyAnchoredWireSplit(d, step.wire, step.witness, step.endpoints, step.target, reservation)
    case 'anchoredWireContract': return applyAnchoredWireContract(d, step.redundant, step.survivor, step.certificate)
    case 'headStrip': return applyHeadStrip(d, step.a, step.b, step.correspondence, reservation)
    case 'closedTermIntro': return applyClosedTermIntro(d, step.region, step.term, reservation)
    case 'fusion': return applyFusion(d, step.wire)
    case 'fission': return applyFission(d, step.node, step.path, reservation)
    case 'comprehensionInstantiate': return applyComprehensionInstantiate(d, step.bubble, step.comp, step.attachments, step.binders, orientation, reservation)
    case 'comprehensionAbstract': return applyComprehensionAbstract(d, step.wrap, step.comp, step.occurrences, orientation, reservation)
    case 'theorem': {
      return applyTheorem(d, ctx, step.name, step.at, step.direction, orientation, reservation)
    }
    case 'vacuousIntro': return applyVacuousBubbleIntro(d, step.sel, step.arity, reservation)
    case 'vacuousElim': return applyVacuousBubbleElim(d, step.region)
    case 'relUnfold': return applyRelUnfold(d, step.node, ctx.relations, reservation)
    case 'relFold': return applyRelFold(d, step.sel, step.defId, step.args, ctx.relations, reservation)
  }
}

/** Execute one step and return its semantic open-interface transport.
 * Graph operations continue to own concrete mutation; this receipt is the
 * single authority for carrying an ordered boundary across that mutation. */
export function applyStepWithReceipt(
  d: Diagram,
  step: ProofStep,
  ctx: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): StepReceipt {
  assertProofContext(ctx)
  const result = applyStepRaw(d, step, ctx, orientation, reservation)
  const survivingSameId = (wire: WireId): WireId | undefined =>
    d.wires[wire] !== undefined && result.wires[wire] !== undefined ? wire : undefined
  const provenance = rootFilteredProvenance(
    result,
    survivingSameId,
  )
  let candidate: (wire: WireId) => WireId | undefined =
    survivingSameId

  if (step.rule === 'wireJoin') {
    const aSurvives = result.wires[step.a] !== undefined
    const retained = aSurvives ? step.a : step.b
    const absorbed = aSurvives ? step.b : step.a
    candidate = (wire) => wire === absorbed
      ? retained
      : survivingSameId(wire)
  } else if (step.rule === 'anchoredWireContract') {
    const redundant = d.nodes[step.redundant]
    const survivor = d.nodes[step.survivor]
    const drop = redundant?.kind === 'term'
      ? Object.keys(d.wires).find((wire) => d.wires[wire]!.endpoints.some((endpoint) =>
          endpoint.node === step.redundant && endpoint.port.kind === 'output'))
      : undefined
    const keep = survivor?.kind === 'term'
      ? Object.keys(d.wires).find((wire) => d.wires[wire]!.endpoints.some((endpoint) =>
          endpoint.node === step.survivor && endpoint.port.kind === 'output'))
      : undefined
    const coalescesAtRoot = drop !== undefined
      && keep !== undefined
      && anchorAvailability(d, step.survivor) === d.root
    candidate = (wire) => wire === drop && coalescesAtRoot
      ? keep
      : survivingSameId(wire)
  } else if (step.rule === 'congruenceJoin') {
    const outputWire = (node: NodeId): WireId | undefined => Object.keys(d.wires).find((wire) =>
      d.wires[wire]!.endpoints.some((endpoint) => endpoint.node === node && endpoint.port.kind === 'output'))
    const aOutput = outputWire(step.a)
    const bOutput = outputWire(step.b)
    const keep = aOutput !== undefined && result.wires[aOutput] !== undefined ? aOutput : bOutput
    const drop = keep === aOutput ? bOutput : aOutput
    candidate = (wire) => wire === drop && keep !== undefined
      ? keep
      : survivingSameId(wire)
  }

  return {
    result,
    provenance,
    interface: rootFilteredInterface(result, candidate),
  }
}

/** Diagram projection for callers that do not carry an open boundary. */
export function applyStep(
  d: Diagram,
  step: ProofStep,
  ctx: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  assertProofContext(ctx)
  return applyStepWithReceipt(d, step, ctx, orientation, reservation).result
}

/**
 * Fold steps over a diagram, naming the failing step on any refusal. The
 * optional onStep invariant runs after every step; its throws propagate
 * unwrapped (they carry their own context).
 */
export function replayProof(
  start: Diagram,
  steps: readonly ProofStep[],
  ctx: ProofContext,
  onStep?: (d: Diagram, stepIndex: number) => void,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  assertProofContext(ctx)
  let cur = start
  steps.forEach((s, i) => {
    try {
      cur = applyStep(cur, s, ctx, orientation)
    } catch (e) {
      throw new ProofError(`step ${i} (${s.rule}) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    onStep?.(cur, i)
  })
  return cur
}
