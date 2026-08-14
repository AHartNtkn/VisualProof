import type { Diagram, NodeId, RegionId } from '../kernel/diagram/diagram'
import { diagramToJson } from '../kernel/diagram/json'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { spliceSubgraphMapped } from '../kernel/diagram/subgraph/splice'
import {
  mkSelection,
  selectionContents,
  type SubgraphSelection,
} from '../kernel/diagram/subgraph/selection'
import { applyAction, singleStepAction, type ProofAction } from '../kernel/proof/action'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import { theoryToJson } from '../kernel/proof/store'
import type { Vec2 } from '../view/vec'
import type { ProofOrientation } from './interact/moves'

export type CopyDestination =
  | { readonly kind: 'edit'; readonly diagram: Diagram; readonly region: RegionId; readonly at: Vec2 }
  | { readonly kind: 'proof'; readonly diagram: Diagram; readonly region: RegionId; readonly orientation: ProofOrientation; readonly ctx: ProofContext }

export type CopyRefusalCode =
  | 'invalid-selection'
  | 'invalid-destination'
  | 'invalid-attachment'
  | 'proof-unavailable'
  | 'stale-source'
  | 'stale-destination'
  | 'invalid-plan'

export type CopyRefusal = {
  readonly ok: false
  readonly kind: 'refusal'
  readonly code: CopyRefusalCode
  readonly message: string
}

export type CopyPlan =
  | { readonly kind: 'edit'; readonly result: Diagram; readonly introduced: readonly NodeId[]; readonly at: Vec2 }
  | { readonly kind: 'proof'; readonly action: ProofAction }

type CopyEvidence = {
  readonly sourceState: string
  readonly destinationState: string
  readonly selection: SubgraphSelection
}

const planEvidence = new WeakMap<CopyPlan, CopyEvidence>()

function deny(code: CopyRefusalCode, message: string): CopyRefusal {
  return Object.freeze({ ok: false as const, kind: 'refusal' as const, code, message })
}

function diagramState(diagram: Diagram): string {
  return JSON.stringify(diagramToJson(diagram))
}

function destinationState(destination: CopyDestination): string {
  switch (destination.kind) {
    case 'edit':
      return JSON.stringify({
        kind: destination.kind,
        diagram: diagramToJson(destination.diagram),
        region: destination.region,
        at: destination.at,
      })
    case 'proof':
      assertProofContext(destination.ctx)
      return JSON.stringify({
        kind: destination.kind,
        diagram: diagramToJson(destination.diagram),
        region: destination.region,
        orientation: destination.orientation,
        context: theoryToJson({
          relations: [...destination.ctx.relations],
          theorems: [...destination.ctx.theorems.values()],
        }),
      })
  }
}

function validateDestination(destination: CopyDestination): CopyRefusal | null {
  if (destination.kind === 'proof') assertProofContext(destination.ctx)
  if (destination.diagram.regions[destination.region] === undefined) {
    return deny('invalid-destination', `copy destination region '${destination.region}' does not exist`)
  }
  if (
    destination.kind === 'edit'
    && (!Number.isFinite(destination.at.x) || !Number.isFinite(destination.at.y))
  ) {
    return deny('invalid-destination', 'copy destination coordinates must be finite')
  }
  return null
}

function finishPlan(
  plan: CopyPlan,
  source: Diagram,
  selection: SubgraphSelection,
  destination: CopyDestination,
): CopyPlan {
  const result = Object.freeze(plan)
  planEvidence.set(result, Object.freeze({
    sourceState: diagramState(source),
    destinationState: destinationState(destination),
    selection: mkSelection(source, selection),
  }))
  return result
}

function planEdit(
  source: Diagram,
  selection: SubgraphSelection,
  destination: Extract<CopyDestination, { readonly kind: 'edit' }>,
): CopyPlan | CopyRefusal {
  try {
    const extraction = extractSubgraph(source, selection)
    const mapped = spliceSubgraphMapped(
      destination.diagram,
      destination.region,
      extraction.pattern,
      extraction.attachments,
    )
    const introduced = Object.keys(mapped.diagram.nodes)
      .filter((node) => destination.diagram.nodes[node] === undefined)
      .sort()
    return finishPlan({
      kind: 'edit',
      result: mapped.diagram,
      introduced: Object.freeze(introduced),
      at: Object.freeze({ ...destination.at }),
    }, source, selection, destination)
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error)
    return deny(
      /attachment wire|attachments|splice/.test(message)
        ? 'invalid-attachment'
        : 'invalid-selection',
      message,
    )
  }
}

function planProof(
  source: Diagram,
  selection: SubgraphSelection,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
): CopyPlan | CopyRefusal {
  if (diagramState(source) !== diagramState(destination.diagram)) {
    return deny('proof-unavailable', 'proof copy is ordinary iteration on the live source diagram')
  }
  const action = singleStepAction('Copy selection', {
    rule: 'iteration',
    sel: selection,
    target: destination.region,
  })
  try {
    applyAction(
      destination.diagram,
      action,
      destination.ctx,
      destination.orientation,
    )
    return finishPlan({
      kind: 'proof',
      action,
    }, source, selection, destination)
  } catch (error) {
    return deny(
      'proof-unavailable',
      error instanceof Error ? error.message : String(error),
    )
  }
}

export function planCopy(
  source: Diagram,
  selection: SubgraphSelection,
  destination: CopyDestination,
): CopyPlan | CopyRefusal {
  const invalid = validateDestination(destination)
  if (invalid !== null) return invalid
  try {
    const contents = selectionContents(source, selection)
    if (
      contents.allRegions.size === 0
      && contents.allNodes.size === 0
      && contents.internalWires.length === 0
    ) return deny('invalid-selection', 'cannot copy an empty selection')
  } catch (error) {
    return deny('invalid-selection', error instanceof Error ? error.message : String(error))
  }
  return destination.kind === 'edit'
    ? planEdit(source, selection, destination)
    : planProof(source, selection, destination)
}

export function revalidateCopy(
  plan: CopyPlan,
  liveSource: Diagram,
  liveDestination: CopyDestination,
): CopyPlan | CopyRefusal {
  const invalid = validateDestination(liveDestination)
  if (invalid !== null) return invalid
  const evidence = planEvidence.get(plan)
  if (evidence === undefined) return deny('invalid-plan', 'copy plan has no revalidation evidence')
  if (diagramState(liveSource) !== evidence.sourceState) {
    return deny('stale-source', 'copy source changed after the plan was created')
  }
  if (destinationState(liveDestination) !== evidence.destinationState) {
    return deny('stale-destination', 'copy destination changed after the plan was created')
  }
  return planCopy(liveSource, evidence.selection, liveDestination)
}
