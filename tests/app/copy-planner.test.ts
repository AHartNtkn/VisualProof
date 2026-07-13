import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { boundaryForm, exploreForm } from '../../src/kernel/diagram/canonical/explore'
import type { Diagram, NodeId, WireId } from '../../src/kernel/diagram/diagram'
import { spawnTermNode } from '../../src/kernel/diagram/spawn'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import { mkSelection, selectionContents, type SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import { applyAction } from '../../src/kernel/proof/action'
import type { ProofContext } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import {
  planCopy,
  revalidateCopy,
  type CopyDestination,
  type CopyPlan,
  type CopyRefusal,
} from '../../src/app/copy-planner'

const p = (source: string) => parseTerm(source)
const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

function refusal(value: CopyPlan | CopyRefusal): CopyRefusal {
  expect(value.kind).toBe('refusal')
  if (value.kind !== 'refusal') throw new Error('expected copy refusal')
  return value
}

function plan(value: CopyPlan | CopyRefusal): CopyPlan {
  expect(value.kind).not.toBe('refusal')
  if (value.kind === 'refusal') throw new Error(value.message)
  return value
}

function crossingFixture(): { diagram: Diagram; selected: NodeId; selection: SubgraphSelection; attachments: readonly WireId[] } {
  const builder = new DiagramBuilder()
  const selected = builder.termNode(builder.root, p('y'))
  const host = builder.termNode(builder.root, p('\\x. x'))
  builder.wire(builder.root, [
    { node: selected, port: { kind: 'freeVar', name: 'y' } },
    { node: host, port: { kind: 'output' } },
  ])
  const diagram = builder.build()
  const selection = mkSelection(diagram, { region: diagram.root, regions: [], nodes: [selected], wires: [] })
  return { diagram, selected, selection, attachments: extractSubgraph(diagram, selection).attachments }
}

function introducedSelection(before: Diagram, after: Diagram, region: string): SubgraphSelection {
  const regions = Object.keys(after.regions).filter((id) => {
    const value = after.regions[id]!
    return before.regions[id] === undefined && value.kind !== 'sheet' && value.parent === region
  })
  const nodes = Object.keys(after.nodes).filter(
    (id) => before.nodes[id] === undefined && after.nodes[id]!.region === region,
  )
  const introducedNodes = new Set(Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined))
  const wires = Object.keys(after.wires).filter((id) => {
    const wire = after.wires[id]!
    return before.wires[id] === undefined
      && wire.scope === region
      && wire.endpoints.every((endpoint) => introducedNodes.has(endpoint.node))
  })
  return mkSelection(after, { region, regions, nodes, wires })
}

describe('CopyPlanner structural destinations', () => {
  it('copies one extracted pattern into a workspace with fresh ids and loose root-scoped crossing wires', () => {
    const source = crossingFixture()
    const draft = new DiagramBuilder().build()
    const beforeSource = JSON.stringify(source.diagram)
    const beforeDraft = JSON.stringify(draft)

    const at = { x: 24, y: 35 }
    const copied = plan(planCopy(source.diagram, source.selection, {
      kind: 'workspace', draft, region: draft.root, at,
    }))

    expect(copied.kind).toBe('workspace')
    if (copied.kind !== 'workspace') throw new Error('expected workspace plan')
    expect(copied.at).toEqual(at)
    expect(copied.introduced).toHaveLength(1)
    expect(copied.introduced).not.toContain(source.selected)
    const introduced = new Set(copied.introduced)
    expect(Object.values(copied.result.wires)).toHaveLength(source.attachments.length)
    expect(Object.values(copied.result.wires).every((wire) =>
      wire.scope === copied.result.root
      && wire.endpoints.length > 0
      && wire.endpoints.every((endpoint) => introduced.has(endpoint.node)),
    )).toBe(true)
    expect(JSON.stringify(source.diagram)).toBe(beforeSource)
    expect(JSON.stringify(draft)).toBe(beforeDraft)
  })

  it('uses the same extraction authority for Edit while preserving every crossing attachment identity', () => {
    const source = crossingFixture()
    const copied = plan(planCopy(source.diagram, source.selection, {
      kind: 'edit', diagram: source.diagram, region: source.diagram.root, at: { x: 3, y: 4 },
    }))

    expect(copied.kind).toBe('edit')
    if (copied.kind !== 'edit') throw new Error('expected Edit plan')
    expect(copied.introduced).toHaveLength(1)
    for (const attachment of source.attachments) {
      expect(copied.result.wires[attachment]).toBeDefined()
      expect(copied.result.wires[attachment]!.endpoints.length)
        .toBe(source.diagram.wires[attachment]!.endpoints.length + 1)
    }
    const alleged = extractSubgraph(
      copied.result,
      introducedSelection(source.diagram, copied.result, source.diagram.root),
    )
    expect(alleged.attachments).toEqual(source.attachments)
    expect(boundaryForm(alleged.pattern)).toBe(boundaryForm(extractSubgraph(source.diagram, source.selection).pattern))
  })
})

describe('CopyPlanner proof destinations', () => {
  it('prefers one genuine iteration action when its existing gate applies', () => {
    const builder = new DiagramBuilder()
    const selected = builder.termNode(builder.root, p('y'))
    const host = builder.termNode(builder.root, p('\\x. x'))
    builder.wire(builder.root, [
      { node: selected, port: { kind: 'freeVar', name: 'y' } },
      { node: host, port: { kind: 'output' } },
    ])
    const target = builder.cut(builder.root)
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: diagram.root, regions: [], nodes: [selected], wires: [] })
    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: target, orientation: 'forward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action).toMatchObject({ label: 'Copy selection', steps: [{ rule: 'iteration', target }] })
    expect(copied.resultFingerprint).toBe(exploreForm(applyAction(diagram, copied.action, ctx, 'forward')))
  })

  it('falls back to a complete ordinary closed-term recipe and proves its exact scratch result', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const selected = builder.termNode(sourceRegion, p('\\x. x'))
    const diagram = builder.build()
    const output = Object.entries(diagram.wires).find(([, wire]) => wire.endpoints[0]?.node === selected)![0]
    const selection = mkSelection(diagram, { region: sourceRegion, regions: [], nodes: [selected], wires: [output] })

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'forward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.label).toBe('Copy selection')
    expect(copied.action.steps.map((step) => step.rule)).toEqual(['closedTermIntro'])
    const replayed = applyAction(diagram, copied.action, ctx, 'forward')
    expect(copied.resultFingerprint).toBe(exploreForm(replayed))
    const alleged = extractSubgraph(replayed, introducedSelection(diagram, replayed, diagram.root))
    expect(alleged.attachments).toEqual([])
    expect(boundaryForm(alleged.pattern)).toBe(boundaryForm(extractSubgraph(diagram, selection).pattern))
  })

  it('compiles paired cuts and bubbles only through their existing contextual introductions', () => {
    const doubleCut = new DiagramBuilder()
    const sourceRegion = doubleCut.cut(doubleCut.root)
    const outer = doubleCut.cut(sourceRegion)
    doubleCut.cut(outer)
    const doubleDiagram = doubleCut.build()
    const doubleSelection = mkSelection(doubleDiagram, { region: sourceRegion, regions: [outer], nodes: [], wires: [] })
    const doublePlan = plan(planCopy(doubleDiagram, doubleSelection, {
      kind: 'proof', diagram: doubleDiagram, region: doubleDiagram.root, orientation: 'forward', ctx,
    }))
    expect(doublePlan.kind).toBe('proof')
    if (doublePlan.kind !== 'proof') throw new Error('expected proof plan')
    expect(doublePlan.action.steps.map((step) => step.rule)).toEqual(['doubleCutIntro'])

    const bubble = new DiagramBuilder()
    const bubbleSource = bubble.cut(bubble.root)
    const selectedBubble = bubble.bubble(bubbleSource, 3)
    const bubbleDiagram = bubble.build()
    const bubbleSelection = mkSelection(bubbleDiagram, { region: bubbleSource, regions: [selectedBubble], nodes: [], wires: [] })
    const bubblePlan = plan(planCopy(bubbleDiagram, bubbleSelection, {
      kind: 'proof', diagram: bubbleDiagram, region: bubbleDiagram.root, orientation: 'forward', ctx,
    }))
    expect(bubblePlan.kind).toBe('proof')
    if (bubblePlan.kind !== 'proof') throw new Error('expected proof plan')
    expect(bubblePlan.action.steps.map((step) => step.rule)).toEqual(['vacuousIntro'])
  })

  it('uses an exact contextual relation constructor for an otherwise unsupported complete pattern', () => {
    const relationBuilder = new DiagramBuilder()
    relationBuilder.cut(relationBuilder.root)
    const relation = mkDiagramWithBoundary(relationBuilder.build(), [])
    const relationCtx: ProofContext = { theorems: new Map(), relations: new Map([['single-cut', relation]]) }

    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const selectedCut = builder.cut(sourceRegion)
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: sourceRegion, regions: [selectedCut], nodes: [], wires: [] })

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'backward', ctx: relationCtx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.steps.map((step) => step.rule)).toEqual(['relationSpawn', 'relUnfold'])
    expect(copied.resultFingerprint).toBe(exploreForm(applyAction(diagram, copied.action, relationCtx, 'backward')))
  })

  it('constructs a bound atom only when its selected binder is recreated in the recipe', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const binder = builder.bubble(sourceRegion, 1)
    builder.atom(binder, binder)
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: sourceRegion, regions: [binder], nodes: [], wires: [] })

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'backward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.steps.map((step) => step.rule)).toEqual(['vacuousIntro', 'boundRelationSpawn'])
    const replayed = applyAction(diagram, copied.action, ctx, 'backward')
    const alleged = extractSubgraph(replayed, introducedSelection(diagram, replayed, diagram.root))
    expect(boundaryForm(alleged.pattern)).toBe(boundaryForm(extractSubgraph(diagram, selection).pattern))
  })

  it('preserves exact crossing identities through valid ordinary spawn and join steps', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const selected = builder.termNode(sourceRegion, p('y'))
    builder.wire(builder.root, [{ node: selected, port: { kind: 'output' } }])
    builder.wire(builder.root, [{ node: selected, port: { kind: 'freeVar', name: 'y' } }])
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: sourceRegion, regions: [], nodes: [selected], wires: [] })
    const sourcePattern = extractSubgraph(diagram, selection)

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'backward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.steps.map((step) => step.rule)).toEqual(['openTermSpawn', 'wireJoin', 'wireJoin'])
    const replayed = applyAction(diagram, copied.action, ctx, 'backward')
    const alleged = extractSubgraph(replayed, introducedSelection(diagram, replayed, diagram.root))
    expect(alleged.attachments).toEqual(sourcePattern.attachments)
    expect(boundaryForm(alleged.pattern)).toBe(boundaryForm(sourcePattern.pattern))
    expect(copied.resultFingerprint).toBe(exploreForm(replayed))
  })

  it('uses fission to construct the exact closed-producer and one-port-consumer normal form', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const producer = builder.termNode(sourceRegion, p('\\x. x'))
    const consumer = builder.termNode(sourceRegion, p('q'))
    builder.wire(sourceRegion, [
      { node: producer, port: { kind: 'output' } },
      { node: consumer, port: { kind: 'freeVar', name: 'q' } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: sourceRegion,
      regions: [],
      nodes: [producer, consumer],
      wires: Object.keys(diagram.wires),
    })

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'forward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.steps.map((step) => step.rule)).toEqual(['closedTermIntro', 'fission'])
    expect(copied.resultFingerprint).toBe(exploreForm(applyAction(diagram, copied.action, ctx, 'forward')))
  })
})

describe('CopyPlanner refusals and revalidation', () => {
  it('rejects an external binder stub unless the binder is included', () => {
    const builder = new DiagramBuilder()
    const binder = builder.bubble(builder.root, 1)
    const selected = builder.atom(binder, binder)
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: binder, regions: [], nodes: [selected], wires: [] })

    const denied = refusal(planCopy(diagram, selection, {
      kind: 'edit', diagram, region: binder, at: { x: 0, y: 0 },
    }))

    expect(denied.code).toBe('external-binder')
    expect(denied).not.toHaveProperty('result')
  })

  it('returns typed whole-plan refusals for unsupported cuts, wrong polarity, and missing attachments', () => {
    const cuts = new DiagramBuilder()
    const cutSource = cuts.cut(cuts.root)
    const loneCut = cuts.cut(cutSource)
    const cutDiagram = cuts.build()
    const cutSelection = mkSelection(cutDiagram, { region: cutSource, regions: [loneCut], nodes: [], wires: [] })
    const unsupported = refusal(planCopy(cutDiagram, cutSelection, {
      kind: 'proof', diagram: cutDiagram, region: cutDiagram.root, orientation: 'forward', ctx,
    }))
    expect(unsupported.code).toBe('unsupported-structure')

    const open = new DiagramBuilder()
    const openSource = open.cut(open.root)
    const openNode = open.termNode(openSource, p('y'))
    open.wire(open.root, [{ node: openNode, port: { kind: 'output' } }])
    open.wire(open.root, [{ node: openNode, port: { kind: 'freeVar', name: 'y' } }])
    const openDiagram = open.build()
    const openSelection = mkSelection(openDiagram, { region: openSource, regions: [], nodes: [openNode], wires: [] })
    const polarity = refusal(planCopy(openDiagram, openSelection, {
      kind: 'proof', diagram: openDiagram, region: openDiagram.root, orientation: 'forward', ctx,
    }))
    expect(polarity.code).toBe('proof-unavailable')

    const missingDestination = new DiagramBuilder().build()
    const attachment = refusal(planCopy(openDiagram, openSelection, {
      kind: 'proof', diagram: missingDestination, region: missingDestination.root, orientation: 'backward', ctx,
    }))
    expect(attachment.code).toBe('invalid-attachment')
    for (const denied of [unsupported, polarity, attachment]) expect(denied).not.toHaveProperty('result')
  })

  it('constructs an endpoint-free selected wire by introducing and erasing only a witness node', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const loose = builder.wire(sourceRegion, [])
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: sourceRegion, regions: [], nodes: [], wires: [loose] })

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'forward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.steps.map((step) => step.rule)).toEqual(['closedTermIntro', 'erasure'])
    const replayed = applyAction(diagram, copied.action, ctx, 'forward')
    expect(copied.resultFingerprint).toBe(exploreForm(replayed))
    expect(Object.values(replayed.wires).filter((wire) => wire.endpoints.length === 0)).toHaveLength(2)
  })

  it('uses a constructed loose survivor for an outer-scoped wire whose endpoints are all descendants', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const outer = builder.cut(sourceRegion)
    builder.cut(outer)
    const selected = builder.termNode(outer, p('\\x. x'))
    const wide = builder.wire(sourceRegion, [{ node: selected, port: { kind: 'output' } }])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: sourceRegion, regions: [outer], nodes: [], wires: [wide],
    })

    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'forward', ctx,
    }))

    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    expect(copied.action.steps.map((step) => step.rule)).toEqual([
      'doubleCutIntro', 'closedTermIntro', 'closedTermIntro', 'erasure', 'wireJoin',
    ])
    expect(copied.resultFingerprint).toBe(exploreForm(applyAction(diagram, copied.action, ctx, 'forward')))
  })

  it('refuses endpoint-free wire construction when the real erasure polarity gate is closed', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const loose = builder.wire(sourceRegion, [])
    const diagram = builder.build()
    const selection = mkSelection(diagram, { region: sourceRegion, regions: [], nodes: [], wires: [loose] })

    const denied = refusal(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'backward', ctx,
    }))
    expect(denied.code).toBe('proof-unavailable')
    expect(denied).not.toHaveProperty('action')
  })

  it('replans unchanged evidence and rejects stale source and destination state separately', () => {
    const source = crossingFixture()
    const destination: CopyDestination = {
      kind: 'edit', diagram: source.diagram, region: source.diagram.root, at: { x: 8, y: 9 },
    }
    const original = plan(planCopy(source.diagram, source.selection, destination))

    expect(revalidateCopy(original, source.diagram, destination).kind).toBe('edit')

    const staleSource = spawnTermNode(source.diagram, source.diagram.root, p('\\x. x')).diagram
    expect(refusal(revalidateCopy(original, staleSource, destination)).code).toBe('stale-source')

    const staleDestinationDiagram = spawnTermNode(destination.diagram, destination.diagram.root, p('\\x. \\y. x')).diagram
    expect(refusal(revalidateCopy(original, source.diagram, {
      ...destination, diagram: staleDestinationDiagram,
    })).code).toBe('stale-destination')
  })

  it('validates complete selection ownership rather than accepting a structurally similar subset', () => {
    const builder = new DiagramBuilder()
    const sourceRegion = builder.cut(builder.root)
    const first = builder.termNode(sourceRegion, p('\\x. x'))
    const second = builder.termNode(sourceRegion, p('\\x. \\y. x'))
    const diagram = builder.build()
    const all = selectionContents(diagram, mkSelection(diagram, {
      region: sourceRegion, regions: [], nodes: [first, second], wires: Object.keys(diagram.wires),
    }))
    expect(all.allNodes.size).toBe(2)
    const selection = mkSelection(diagram, {
      region: sourceRegion, regions: [], nodes: [first, second], wires: Object.keys(diagram.wires),
    })
    const copied = plan(planCopy(diagram, selection, {
      kind: 'proof', diagram, region: diagram.root, orientation: 'forward', ctx,
    }))
    expect(copied.kind).toBe('proof')
    if (copied.kind !== 'proof') throw new Error('expected proof plan')
    const replayed = applyAction(diagram, copied.action, ctx, 'forward')
    expect(Object.keys(replayed.nodes)).toHaveLength(Object.keys(diagram.nodes).length + 2)
  })
})
