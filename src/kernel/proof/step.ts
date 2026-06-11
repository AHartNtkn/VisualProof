import type { Term } from '../term/term'
import type { PathSeg } from '../term/reduce'
import type { ConversionCertificate } from '../term/certificate'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { applyInsertion, applyWireJoin } from '../rules/insertion'
import { applyErasure, applyWireSever } from '../rules/erasure'
import { applyIteration, applyDeiteration } from '../rules/iteration'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../rules/doublecut'
import { applyConversionByCertificate } from '../rules/conversion'
import { applyCongruenceJoin } from '../rules/congruence'
import { applyFusion, applyFission } from '../rules/fusion'
import { applyUnfold, applyFold } from '../rules/definitions'
import type { Definitions } from '../rules/definitions'
import { applyComprehensionInstantiate, applyComprehensionAbstract } from '../rules/comprehension'
import type { AbstractionOccurrence } from '../rules/comprehension'
import { applyVacuousBubbleIntro, applyVacuousBubbleElim } from '../rules/vacuous'
import type { Theorem, TheoremApplication } from './theorem'
import { applyTheorem } from './theorem'
import { ProofError } from './error'

export type ProofContext = {
  readonly definitions: Definitions
  readonly theorems: ReadonlyMap<string, Theorem>
}

/**
 * One serializable rule application. Replay carries no trust: applyStep calls
 * the real appliers, each enforcing its own gate. Conversion replays by
 * certificate (fuel-free, §3.7); deiteration records its fuel (the matcher is
 * deterministic, so replay reproduces the original search).
 */
export type ProofStep =
  | { readonly rule: 'insertion'; readonly region: RegionId; readonly pattern: DiagramWithBoundary; readonly attachments: readonly WireId[]; readonly binders: Readonly<Record<RegionId, RegionId>> }
  | { readonly rule: 'wireJoin'; readonly a: WireId; readonly b: WireId }
  | { readonly rule: 'erasure'; readonly sel: SubgraphSelection }
  | { readonly rule: 'wireSever'; readonly wire: WireId; readonly keep: readonly Endpoint[] }
  | { readonly rule: 'iteration'; readonly sel: SubgraphSelection; readonly target: RegionId }
  | { readonly rule: 'deiteration'; readonly sel: SubgraphSelection; readonly fuel: number }
  | { readonly rule: 'doubleCutIntro'; readonly sel: SubgraphSelection }
  | { readonly rule: 'doubleCutElim'; readonly region: RegionId }
  | { readonly rule: 'conversion'; readonly node: NodeId; readonly term: Term; readonly certificate: ConversionCertificate; readonly attachments: Readonly<Record<string, WireId>> }
  | { readonly rule: 'congruenceJoin'; readonly a: NodeId; readonly b: NodeId; readonly certificate: ConversionCertificate }
  | { readonly rule: 'fusion'; readonly wire: WireId }
  | { readonly rule: 'fission'; readonly node: NodeId; readonly path: readonly PathSeg[] }
  | { readonly rule: 'unfold'; readonly node: NodeId; readonly path: readonly PathSeg[] }
  | { readonly rule: 'fold'; readonly node: NodeId; readonly path: readonly PathSeg[]; readonly constId: string }
  | { readonly rule: 'comprehensionInstantiate'; readonly bubble: RegionId; readonly comp: DiagramWithBoundary; readonly binders: Readonly<Record<RegionId, RegionId>> }
  | { readonly rule: 'comprehensionAbstract'; readonly wrap: SubgraphSelection; readonly comp: DiagramWithBoundary; readonly occurrences: readonly AbstractionOccurrence[] }
  | { readonly rule: 'theorem'; readonly name: string; readonly at: TheoremApplication; readonly direction: 'forward' | 'reverse' }
  | { readonly rule: 'vacuousIntro'; readonly sel: SubgraphSelection; readonly arity: number }
  | { readonly rule: 'vacuousElim'; readonly region: RegionId }

export function applyStep(d: Diagram, step: ProofStep, ctx: ProofContext): Diagram {
  switch (step.rule) {
    case 'insertion': return applyInsertion(d, step.region, step.pattern, step.attachments, new Map(Object.entries(step.binders)))
    case 'wireJoin': return applyWireJoin(d, step.a, step.b)
    case 'erasure': return applyErasure(d, step.sel)
    case 'wireSever': return applyWireSever(d, step.wire, step.keep)
    case 'iteration': return applyIteration(d, step.sel, step.target)
    case 'deiteration': return applyDeiteration(d, step.sel, step.fuel)
    case 'doubleCutIntro': return applyDoubleCutIntro(d, step.sel)
    case 'doubleCutElim': return applyDoubleCutElim(d, step.region)
    case 'conversion': return applyConversionByCertificate(d, step.node, step.term, step.certificate, step.attachments)
    case 'congruenceJoin': return applyCongruenceJoin(d, step.a, step.b, step.certificate)
    case 'fusion': return applyFusion(d, step.wire)
    case 'fission': return applyFission(d, step.node, step.path)
    case 'unfold': return applyUnfold(d, ctx.definitions, step.node, step.path)
    case 'fold': return applyFold(d, ctx.definitions, step.node, step.path, step.constId)
    case 'comprehensionInstantiate': return applyComprehensionInstantiate(d, step.bubble, step.comp, new Map(Object.entries(step.binders)))
    case 'comprehensionAbstract': return applyComprehensionAbstract(d, step.wrap, step.comp, step.occurrences)
    case 'theorem': {
      const thm = ctx.theorems.get(step.name)
      if (thm === undefined) throw new ProofError(`unknown theorem '${step.name}'`)
      return applyTheorem(d, thm, step.at, step.direction)
    }
    case 'vacuousIntro': return applyVacuousBubbleIntro(d, step.sel, step.arity)
    case 'vacuousElim': return applyVacuousBubbleElim(d, step.region)
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
): Diagram {
  let cur = start
  steps.forEach((s, i) => {
    try {
      cur = applyStep(cur, s, ctx)
    } catch (e) {
      throw new ProofError(`step ${i} (${s.rule}) failed: ${e instanceof Error ? e.message : String(e)}`)
    }
    onStep?.(cur, i)
  })
  return cur
}
