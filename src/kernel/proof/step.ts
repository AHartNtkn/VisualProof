import type { Term } from '../term/term'
import type { PathSeg } from '../term/reduce'
import type { ConversionCertificate } from '../term/certificate'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram/diagram'
import type { IdReservation } from '../diagram/subgraph/freshId'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import { applyWireJoin } from '../rules/wire-join'
import { applyOpenTermSpawn, applyRelationSpawn, applyBoundRelationSpawn } from '../rules/spawn'
import { applyErasure, applyWireSever } from '../rules/erasure'
import { applyIteration, applyDeiteration } from '../rules/iteration'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../rules/doublecut'
import { applyConversionByCertificate } from '../rules/conversion'
import { applyCongruenceJoin } from '../rules/congruence'
import { applyAnchoredWireSplit, applyAnchoredWireContract } from '../rules/anchored-wire'
import { applyHeadStrip } from '../rules/headstrip'
import { applyClosedTermIntro } from '../rules/intro'
import { applyFusion, applyFission } from '../rules/fusion'
import { applyComprehensionInstantiate, applyComprehensionAbstract } from '../rules/comprehension'
import type { AbstractionOccurrence } from '../rules/comprehension'
import { applyVacuousBubbleIntro, applyVacuousBubbleElim } from '../rules/vacuous'
import { applyRelUnfold, applyRelFold } from '../rules/reldef'
import type { Theorem, TheoremApplication } from './theorem'
import { applyTheorem } from './theorem'
import { ProofError } from './error'

export type ProofContext = {
  readonly theorems: ReadonlyMap<string, Theorem>
  /** Named relations (comprehension bodies) resolvable by relUnfold/relFold. */
  readonly relations: ReadonlyMap<string, DiagramWithBoundary>
}

/**
 * One serializable rule application. Replay carries no trust: applyStep calls
 * the real appliers, each enforcing its own gate. Conversion replays by
 * certificates. Replay is entirely fuel-free and never reruns proof search.
 */
export type ProofStep =
  | { readonly rule: 'openTermSpawn'; readonly region: RegionId; readonly term: Term }
  | { readonly rule: 'relationSpawn'; readonly region: RegionId; readonly defId: string; readonly arity: number }
  | { readonly rule: 'boundRelationSpawn'; readonly region: RegionId; readonly binder: RegionId; readonly arity: number }
  | { readonly rule: 'wireJoin'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'erasure'; readonly sel: SubgraphSelection }
  | { readonly rule: 'wireSever'; readonly wire: WireId; readonly keep: readonly Endpoint[] }
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly justifier: SubgraphSelection; readonly certificate: OccurrenceCertificate }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'conversion'; readonly node: NodeId; readonly term: Term; readonly certificate: ConversionCertificate; readonly attachments: Readonly<Record<string, WireId>> }
  | { readonly rule: 'congruenceJoin'; readonly a: NodeId; readonly b: NodeId; readonly certificate: ConversionCertificate }
  | { readonly rule: 'anchoredWireSplit'; readonly wire: WireId; readonly witness: NodeId; readonly endpoints: readonly Endpoint[]; readonly target: RegionId }
  | { readonly rule: 'anchoredWireContract'; readonly redundant: NodeId; readonly survivor: NodeId; readonly certificate: ConversionCertificate }
  | { readonly rule: 'headStrip'; readonly a: NodeId; readonly b: NodeId }
  | { readonly rule: 'closedTermIntro'; readonly region: RegionId; readonly term: Term }
  | { readonly rule: 'fusion'; readonly wire: WireId }
  | { readonly rule: 'fission'; readonly node: NodeId; readonly path: readonly PathSeg[] }
  | { readonly rule: 'comprehensionInstantiate'; readonly bubble: RegionId; readonly comp: DiagramWithBoundary; readonly attachments: readonly WireId[]; readonly binders: Readonly<Record<RegionId, RegionId>> }
  | { readonly rule: 'comprehensionAbstract'; readonly wrap: SubgraphSelection; readonly comp: DiagramWithBoundary; readonly occurrences: readonly AbstractionOccurrence[] }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }
  | { readonly rule: 'vacuousIntro'; readonly sel: SubgraphSelection; readonly arity: number }
  | { readonly rule: 'vacuousElim'; readonly region: RegionId }
  | { readonly rule: 'relUnfold'; readonly node: NodeId }
  | { readonly rule: 'relFold'; readonly sel: SubgraphSelection; readonly defId: string; readonly args: readonly WireId[] }

/**
 * Apply one step. `orientation` is the reasoning direction: 'forward' (the
 * default — replay and forward proving) keeps every gate as stated;
 * 'backward' (acting on a GOAL) flips exactly the polarity-tied gates
 * (erasure, atomic spawning, wire joining, theorem citation) — the calculus's cut symmetry.
 * Execution is IDENTICAL either way: one applier per rule, no mirrors.
 */
export function applyStep(
  d: Diagram,
  step: ProofStep,
  ctx: ProofContext,
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  switch (step.rule) {
    case 'openTermSpawn': return applyOpenTermSpawn(d, step.region, step.term, orientation, reservation)
    case 'relationSpawn': return applyRelationSpawn(d, step.region, step.defId, step.arity, ctx.relations, orientation, reservation)
    case 'boundRelationSpawn': return applyBoundRelationSpawn(d, step.region, step.binder, step.arity, orientation, reservation)
    case 'wireJoin': return applyWireJoin(d, step.a, step.b, orientation)
    case 'erasure': return applyErasure(d, step.sel, orientation)
    case 'wireSever': return applyWireSever(d, step.wire, step.keep, orientation, reservation)
    case 'iteration': return applyIteration(d, step.sel, step.target, reservation)
    case 'deiteration': return applyDeiteration(d, step.sel, step.justifier, step.certificate)
    case 'doubleCutIntro': return applyDoubleCutIntro(d, step.sel, reservation)
    case 'doubleCutElim': return applyDoubleCutElim(d, step.region)
    case 'conversion': return applyConversionByCertificate(d, step.node, step.term, step.certificate, step.attachments, reservation)
    case 'congruenceJoin': return applyCongruenceJoin(d, step.a, step.b, step.certificate)
    case 'anchoredWireSplit': return applyAnchoredWireSplit(d, step.wire, step.witness, step.endpoints, step.target, reservation)
    case 'anchoredWireContract': return applyAnchoredWireContract(d, step.redundant, step.survivor, step.certificate)
    case 'headStrip': return applyHeadStrip(d, step.a, step.b, reservation)
    case 'closedTermIntro': return applyClosedTermIntro(d, step.region, step.term, reservation)
    case 'fusion': return applyFusion(d, step.wire)
    case 'fission': return applyFission(d, step.node, step.path, reservation)
    case 'comprehensionInstantiate': return applyComprehensionInstantiate(d, step.bubble, step.comp, step.attachments, new Map(Object.entries(step.binders)), orientation, reservation)
    case 'comprehensionAbstract': return applyComprehensionAbstract(d, step.wrap, step.comp, step.occurrences, orientation, reservation)
    case 'theorem': {
      const thm = ctx.theorems.get(step.name)
      if (thm === undefined) throw new ProofError(`unknown theorem '${step.name}'`)
      return applyTheorem(d, thm, step.at, step.direction, orientation, reservation)
    }
    case 'vacuousIntro': return applyVacuousBubbleIntro(d, step.sel, step.arity, reservation)
    case 'vacuousElim': return applyVacuousBubbleElim(d, step.region)
    case 'relUnfold': return applyRelUnfold(d, step.node, ctx.relations, reservation)
    case 'relFold': return applyRelFold(d, step.sel, step.defId, step.args, ctx.relations, reservation)
  }
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
