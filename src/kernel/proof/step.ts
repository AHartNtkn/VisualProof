import type {
  Diagram,
  DiagramNormalization,
  NodeId,
  RegionId,
  WireId,
} from '../diagram/diagram'
import { captureDiagramNormalizations } from '../diagram/diagram'
import { isAncestorOrEqual } from '../diagram/regions'
import type { RelSig, Sig } from '../diagram/sig'
import {
  createIdMintRecorder,
  freezeIdMintLog,
  withIdMintCapture,
  type IdMintLog,
  type IdReservation,
} from '../diagram/subgraph/freshId'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { applyDoubleCutElim, applyDoubleCutIntro } from '../rules/doublecut'
import { applyErasure } from '../rules/erasure'
import { applyFold, applyUnfold } from '../rules/fold'
import { applyIdentityInsertion } from '../rules/identity'
import {
  applyDeiteration,
  applyIteration,
  type IdentityRetarget,
} from '../rules/iteration'
import { applyRefSpawn, applyAtomSpawn } from '../rules/spawn'
import { applyVacuousElim, applyVacuousIntro } from '../rules/vacuous'
import {
  applyCutAbsorb,
  applyCutWrap,
  applyEndsDelete,
  applyEndsSpawn,
  applyParallelFuse,
  applyParallelSplit,
  type EndSite,
} from '../rules/wire-content'
import {
  applyWireJoin,
  applyWireSever,
  type WireJoinInput,
  type WireSeverInput,
} from '../rules/wire-quantifier'
import { assertProofContext, type ProofContext } from './context'
import { ProofError } from './error'
import { applyTheorem, type TheoremApplication } from './theorem'

/** One replayable Phase-1 primitive. This union is the durable proof language. */
export type ProofStep =
  | { readonly rule: 'refSpawn'; readonly region: RegionId; readonly defId: string; readonly sig: RelSig }
  | { readonly rule: 'atomSpawn'; readonly region: RegionId; readonly wire: WireId }
  | { readonly rule: 'identityInsert'; readonly region: RegionId; readonly wires: readonly WireId[] }
  | { readonly rule: 'wireJoin'; readonly input: WireJoinInput }
  | { readonly rule: 'erasure'; readonly sel: SubgraphSelection }
  | { readonly rule: 'wireSever'; readonly input: WireSeverInput }
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId; readonly retargets: readonly IdentityRetarget[] }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly justifier: SubgraphSelection; readonly certificate: OccurrenceCertificate; readonly retargets: readonly IdentityRetarget[] }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }
  | { readonly rule: 'vacuousIntro'; readonly scope: RegionId; readonly sig: Sig }
  | { readonly rule: 'vacuousElim'; readonly wireId: WireId }
  | { readonly rule: 'unfold'; readonly nodeId: NodeId }
  | { readonly rule: 'fold'; readonly occurrence: SubgraphSelection; readonly args: readonly WireId[]; readonly defId: string }
  | { readonly rule: 'cutWrap'; readonly wire: WireId }
  | { readonly rule: 'cutAbsorb'; readonly wire: WireId }
  | { readonly rule: 'parallelSplit'; readonly wire: WireId }
  | { readonly rule: 'parallelFuse'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'endsDelete'; readonly wire: WireId }
  | { readonly rule: 'endsSpawn'; readonly wire: WireId; readonly sites: readonly EndSite[] }

/** Logical transport of source wire identities through one proof step. */
export type WireInterfaceTransport = {
  readonly image: (wire: WireId) => WireId | undefined
}

/** Injective graph provenance: only the same surviving source ID is retained. */
export type WireProvenance = {
  readonly image: (wire: WireId) => WireId | undefined
}

export type StepReceipt = {
  readonly result: Diagram
  /** Every graph ID minted by this step, before normalization. */
  readonly allocation: IdMintLog
  readonly provenance: WireProvenance
  readonly interface: WireInterfaceTransport
  /**
   * Total wire transport at every scope: the surviving name of any wire the
   * step consumed or minted, or undefined when nothing survives it.
   */
  readonly transport: WireInterfaceTransport
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

function rootImage(
  target: Diagram,
  candidate: WireId | undefined,
): WireId | undefined {
  if (candidate === undefined) return undefined
  return target.wires[candidate]?.scope === target.root ? candidate : undefined
}

function applyStepRaw(
  diagram: Diagram,
  step: ProofStep,
  context: ProofContext,
  orientation: 'forward' | 'backward',
  reservation?: IdReservation,
): Diagram {
  switch (step.rule) {
    case 'refSpawn':
      return applyRefSpawn(
        diagram,
        step.region,
        step.defId,
        step.sig,
        context.relations,
        orientation,
        reservation,
      )
    case 'atomSpawn':
      return applyAtomSpawn(
        diagram,
        step.region,
        step.wire,
        orientation,
        reservation,
      )
    case 'identityInsert':
      return applyIdentityInsertion(
        diagram,
        step.region,
        step.wires,
        orientation,
        reservation,
      )
    case 'wireJoin':
      return applyWireJoin(
        diagram,
        step.input,
        orientation,
        reservation,
      )
    case 'erasure':
      return applyErasure(diagram, step.sel, orientation)
    case 'wireSever':
      return applyWireSever(
        diagram,
        step.input,
        orientation,
        reservation,
      )
    case 'iteration':
      return applyIteration(
        diagram,
        step.sel,
        step.target,
        step.retargets,
        reservation,
      )
    case 'deiteration':
      return applyDeiteration(
        diagram,
        step.sel,
        step.justifier,
        step.certificate,
        step.retargets,
      )
    case 'doubleCutIntro':
      return applyDoubleCutIntro(diagram, step.sel, reservation)
    case 'doubleCutElim':
      return applyDoubleCutElim(diagram, step.region)
    case 'theorem':
      return applyTheorem(
        diagram,
        context,
        step.name,
        step.at,
        step.direction,
        orientation,
        reservation,
      )
    case 'vacuousIntro':
      return applyVacuousIntro(
        diagram,
        step.scope,
        step.sig,
        reservation,
      )
    case 'vacuousElim':
      return applyVacuousElim(diagram, step.wireId)
    case 'unfold':
      return applyUnfold(
        diagram,
        step.nodeId,
        context.relations,
        reservation,
      )
    case 'fold':
      return applyFold(
        diagram,
        step.occurrence,
        step.args,
        step.defId,
        context.relations,
        reservation,
      )
    case 'cutWrap':
      return applyCutWrap(diagram, step.wire, reservation)
    case 'cutAbsorb':
      return applyCutAbsorb(diagram, step.wire, reservation)
    case 'parallelSplit':
      return applyParallelSplit(diagram, step.wire, reservation)
    case 'parallelFuse':
      return applyParallelFuse(diagram, step.a, step.b, reservation)
    case 'endsDelete':
      return applyEndsDelete(diagram, step.wire, orientation)
    case 'endsSpawn':
      return applyEndsSpawn(
        diagram,
        step.wire,
        step.sites,
        orientation,
        reservation,
      )
  }
}

function joinedRepresentative(
  diagram: Diagram,
  step: ProofStep,
  wire: WireId,
): WireId {
  if (step.rule !== 'wireJoin' || step.input.kind !== 'iota') return wire
  const a = diagram.wires[step.input.a]
  const b = diagram.wires[step.input.b]
  if (a === undefined || b === undefined) return wire
  const retained = isAncestorOrEqual(diagram, a.scope, b.scope)
    ? step.input.a
    : step.input.b
  return wire === step.input.a || wire === step.input.b ? retained : wire
}

function composeNormalizationWireImage(
  source: WireId,
  normalizations: readonly DiagramNormalization[],
): WireId | undefined {
  let current: WireId | undefined = source
  for (const normalization of normalizations) {
    if (current === undefined || !normalization.wireImage.has(current)) {
      return undefined
    }
    current = normalization.wireImage.get(current)
  }
  return current
}

/**
 * Execute one primitive and compose its wire receipt in the required order:
 * rule-intent, identity canonicalization, then root visibility.
 */
export function applyStepWithReceipt(
  diagram: Diagram,
  step: ProofStep,
  context: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): StepReceipt {
  assertProofContext(context)
  const allocation = createIdMintRecorder()
  const capturedReservation = withIdMintCapture(reservation, allocation)
  const captured = captureDiagramNormalizations(
    () => applyStepRaw(
      diagram,
      step,
      context,
      orientation,
      capturedReservation,
    ),
  )
  const result = captured.result
  const interfaceImage = (source: WireId): WireId | undefined => {
    if (diagram.wires[source] === undefined) return undefined
    const intentional = joinedRepresentative(diagram, step, source)
    return rootImage(
      result,
      composeNormalizationWireImage(intentional, captured.normalizations),
    )
  }
  const provenanceImage = (source: WireId): WireId | undefined =>
    diagram.wires[source] !== undefined
    && result.wires[source] !== undefined
    && result.wires[source]!.scope === result.root
      ? source
      : undefined
  const transportImage = (source: WireId): WireId | undefined => {
    const image = composeNormalizationWireImage(
      joinedRepresentative(diagram, step, source),
      captured.normalizations,
    )
    return image !== undefined && result.wires[image] !== undefined
      ? image
      : undefined
  }

  return {
    result,
    allocation: freezeIdMintLog(allocation),
    provenance: { image: provenanceImage },
    interface: { image: interfaceImage },
    transport: { image: transportImage },
  }
}

export function applyStep(
  diagram: Diagram,
  step: ProofStep,
  context: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  return applyStepWithReceipt(
    diagram,
    step,
    context,
    orientation,
    reservation,
  ).result
}

export function replayProof(
  start: Diagram,
  steps: readonly ProofStep[],
  context: ProofContext,
  onStep?: (diagram: Diagram, stepIndex: number) => void,
  orientation: 'forward' | 'backward' = 'forward',
): Diagram {
  assertProofContext(context)
  let current = start
  steps.forEach((step, index) => {
    try {
      current = applyStep(current, step, context, orientation)
    } catch (error) {
      throw new ProofError(
        `step ${index} (${step.rule}) failed: `
        + `${error instanceof Error ? error.message : String(error)}`,
      )
    }
    onStep?.(current, index)
  })
  return current
}
