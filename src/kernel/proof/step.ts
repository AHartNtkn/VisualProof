import type {
  Diagram,
  NodeId,
  RegionId,
  WireId,
} from '../diagram/diagram'
import { derivedScope, isAncestorOrEqual } from '../diagram/regions'
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
} from '../rules/iteration'
import { applyRefSpawn, applyAtomSpawn } from '../rules/spawn'
import {
  applyIdentification,
  applyPresentation,
  applyVacuityDelete,
  applyVacuityInsert,
  type IdentificationInput,
  type PresentationInput,
  type VacuityInstance,
} from '../rules/identity-rules'
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
  applyAbstractFormal,
  applyApplyFormal,
  applyArgContract,
  applyArgDrop,
  applyArgDuplicate,
  applyArgExtend,
  applyArgPermute,
  applyArityShift,
  applyArityUnshift,
  applyIdentityAbstract,
  applyIdentityLeaf,
  applyRefAbstract,
  applyRefLeaf,
} from '../rules/wire-args'
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
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly justifier: SubgraphSelection; readonly certificate: OccurrenceCertificate }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }
  | { readonly rule: 'vacuity'; readonly direction: 'insert' | 'delete'; readonly instance: VacuityInstance }
  | { readonly rule: 'presentation'; readonly input: PresentationInput }
  | { readonly rule: 'identification'; readonly input: IdentificationInput }
  | { readonly rule: 'unfold'; readonly nodeId: NodeId }
  | { readonly rule: 'fold'; readonly occurrence: SubgraphSelection; readonly args: readonly WireId[]; readonly defId: string }
  | { readonly rule: 'cutWrap'; readonly wire: WireId }
  | { readonly rule: 'cutAbsorb'; readonly wire: WireId }
  | { readonly rule: 'parallelSplit'; readonly wire: WireId }
  | { readonly rule: 'parallelFuse'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'endsDelete'; readonly wire: WireId }
  | { readonly rule: 'endsSpawn'; readonly wire: WireId; readonly sites: readonly EndSite[] }
  | { readonly rule: 'arityShift'; readonly wire: WireId; readonly newArgSig: Sig }
  | { readonly rule: 'arityUnshift'; readonly wire: WireId; readonly position: number }
  | { readonly rule: 'argPermute'; readonly wire: WireId; readonly permutation: readonly number[] }
  | { readonly rule: 'argDuplicate'; readonly wire: WireId; readonly position: number }
  | { readonly rule: 'argContract'; readonly wire: WireId; readonly position: number }
  | { readonly rule: 'argDrop'; readonly wire: WireId; readonly position: number }
  | { readonly rule: 'argExtend'; readonly wire: WireId; readonly position: number; readonly newArgSig: Sig; readonly attachments: Readonly<Record<NodeId, WireId>> }
  | { readonly rule: 'applyFormal'; readonly wire: WireId; readonly position: number }
  | { readonly rule: 'abstractFormal'; readonly ends: readonly NodeId[]; readonly scope: RegionId }
  | { readonly rule: 'identityLeaf'; readonly wire: WireId }
  | { readonly rule: 'identityAbstract'; readonly nodes: readonly NodeId[]; readonly scope: RegionId }
  | { readonly rule: 'refLeaf'; readonly wire: WireId; readonly defId: string }
  | { readonly rule: 'refAbstract'; readonly nodes: readonly NodeId[]; readonly scope: RegionId }

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
  /** Every graph ID minted by this step. */
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
  if (candidate === undefined || target.wires[candidate] === undefined) return undefined
  return derivedScope(target, candidate) === target.root ? candidate : undefined
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
      return applyWireJoin(diagram, step.input, orientation)
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
        reservation,
      )
    case 'deiteration':
      return applyDeiteration(
        diagram,
        step.sel,
        step.justifier,
        step.certificate,
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
    case 'vacuity':
      return step.direction === 'insert'
        ? applyVacuityInsert(diagram, step.instance, reservation)
        : applyVacuityDelete(diagram, step.instance)
    case 'presentation':
      return applyPresentation(diagram, step.input, reservation)
    case 'identification':
      return applyIdentification(diagram, step.input, reservation)
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
    case 'arityShift':
      return applyArityShift(diagram, step.wire, step.newArgSig, reservation)
    case 'arityUnshift':
      return applyArityUnshift(diagram, step.wire, step.position)
    case 'argPermute':
      return applyArgPermute(diagram, step.wire, step.permutation, reservation)
    case 'argDuplicate':
      return applyArgDuplicate(diagram, step.wire, step.position, reservation)
    case 'argContract':
      return applyArgContract(diagram, step.wire, step.position, reservation)
    case 'argDrop':
      return applyArgDrop(
        diagram,
        step.wire,
        step.position,
        orientation,
        reservation,
      )
    case 'argExtend':
      return applyArgExtend(
        diagram,
        step.wire,
        step.position,
        step.newArgSig,
        new Map(Object.entries(step.attachments)),
        orientation,
        reservation,
      )
    case 'applyFormal':
      return applyApplyFormal(
        diagram,
        step.wire,
        step.position,
        orientation,
        reservation,
      )
    case 'abstractFormal':
      return applyAbstractFormal(
        diagram,
        step.ends,
        step.scope,
        orientation,
        reservation,
      )
    case 'identityLeaf':
      return applyIdentityLeaf(diagram, step.wire, orientation, reservation)
    case 'identityAbstract':
      return applyIdentityAbstract(
        diagram,
        step.nodes,
        step.scope,
        orientation,
        reservation,
      )
    case 'refLeaf':
      return applyRefLeaf(
        diagram,
        step.wire,
        step.defId,
        context.relations,
        orientation,
        reservation,
      )
    case 'refAbstract':
      return applyRefAbstract(
        diagram,
        step.nodes,
        step.scope,
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
  if (step.rule === 'identification' && step.input.kind === 'collapse') {
    return step.input.absorbed.includes(wire) ? step.input.survivor : wire
  }
  if (step.rule !== 'wireJoin') return wire
  const a = diagram.wires[step.input.a]
  const b = diagram.wires[step.input.b]
  if (a === undefined || b === undefined) return wire
  const retained = isAncestorOrEqual(
    diagram,
    derivedScope(diagram, step.input.a),
    derivedScope(diagram, step.input.b),
  )
    ? step.input.a
    : step.input.b
  return wire === step.input.a || wire === step.input.b ? retained : wire
}

/**
 * Execute one primitive and compose its wire receipt: rule-intent, then
 * root visibility. Wire ids are stable — no rule renames a wire it does not
 * delete — so no further image composition exists.
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
  const result = applyStepRaw(
    diagram,
    step,
    context,
    orientation,
    capturedReservation,
  )
  const interfaceImage = (source: WireId): WireId | undefined => {
    if (diagram.wires[source] === undefined) return undefined
    return rootImage(result, joinedRepresentative(diagram, step, source))
  }
  const provenanceImage = (source: WireId): WireId | undefined =>
    diagram.wires[source] !== undefined
    && result.wires[source] !== undefined
    && derivedScope(result, source) === result.root
      ? source
      : undefined
  const transportImage = (source: WireId): WireId | undefined => {
    const image = joinedRepresentative(diagram, step, source)
    return result.wires[image] !== undefined ? image : undefined
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
