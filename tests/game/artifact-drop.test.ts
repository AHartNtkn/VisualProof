import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { artifactTheoremContext } from '../../src/game/artifact-theorem'
import { planArtifactDrop } from '../../src/game/interface/artifact-drop'
import { minimalPuzzle } from './catalog-fixture'
import { twoVeils } from './fixtures'

const artifactGoal = twoVeils()
const artifact = minimalPuzzle({ goal: artifactGoal.goal })
const completed = artifactTheoremContext(
  [artifact],
  new Set([artifact.id]),
  { relations: new Map() },
)

describe('completed artifact drop authority', () => {
  it('dissolves a cut-only exact occurrence through an ordinary reverse theorem step', () => {
    const result = planArtifactDrop({
      artifact,
      diagram: artifact.goal.diagram,
      context: completed,
      target: {
        hit: { kind: 'region', id: artifactGoal.eliminations[0]! },
        containingRegion: artifact.goal.diagram.root,
      },
      fuel: 256,
    })

    expect(result).toMatchObject({
      ok: true,
      operation: 'dissolve',
      step: { rule: 'theorem', direction: 'reverse' },
    })
    if (!result.ok) throw new Error(result.reason)
    expect(Object.keys(applyStep(artifact.goal.diagram, result.step, completed, 'backward').regions))
      .toEqual([artifact.goal.diagram.root])
  })

  it('manifests into the actual smallest negative containing region', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const diagram = host.build()
    const result = planArtifactDrop({
      artifact,
      diagram,
      context: completed,
      target: { hit: { kind: 'region', id: negative }, containingRegion: negative },
      fuel: 256,
    })

    expect(result).toMatchObject({
      ok: true,
      operation: 'manifest',
      step: {
        rule: 'theorem',
        direction: 'forward',
        at: { sel: { region: negative, regions: [], nodes: [], wires: [] }, args: [] },
      },
    })
    if (!result.ok) throw new Error(result.reason)
    expect(Object.values(applyStep(diagram, result.step, completed, 'backward').regions)
      .filter((region) => region.kind === 'cut')).toHaveLength(3)
  })

  it('refuses incomplete artifacts, similar forms, and strict-subgraph hits without a step', () => {
    const unavailable = artifactTheoremContext([artifact], new Set(), { relations: new Map() })
    expect(planArtifactDrop({
      artifact,
      diagram: artifact.goal.diagram,
      context: unavailable,
      target: { hit: { kind: 'region', id: artifactGoal.eliminations[0]! }, containingRegion: artifact.goal.diagram.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'artifact-incomplete' })

    const similar = new DiagramBuilder()
    const onlyCut = similar.cut(similar.root)
    const similarDiagram = similar.build()
    expect(planArtifactDrop({
      artifact,
      diagram: similarDiagram,
      context: completed,
      target: { hit: { kind: 'region', id: onlyCut }, containingRegion: similar.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })

    expect(planArtifactDrop({
      artifact,
      diagram: artifact.goal.diagram,
      context: completed,
      target: { hit: null, containingRegion: artifact.goal.diagram.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })
  })

  it('does not turn a substantive wrong hit into manifestation in an otherwise eligible field', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const wrongNode = host.termNode(negative, parseTerm('x'))
    const diagram = host.build()

    expect(planArtifactDrop({
      artifact,
      diagram,
      context: completed,
      target: { hit: { kind: 'node', id: wrongNode }, containingRegion: negative },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })
  })

  it('selects one of several exact occurrences only from the pointer hit', () => {
    const host = new DiagramBuilder()
    const left = host.cut(host.root)
    host.cut(left)
    const right = host.cut(host.root)
    host.cut(right)
    const diagram = host.build()

    const leftPlan = planArtifactDrop({
      artifact,
      diagram,
      context: completed,
      target: { hit: { kind: 'region', id: left }, containingRegion: host.root },
      fuel: 256,
    })
    const rightPlan = planArtifactDrop({
      artifact,
      diagram,
      context: completed,
      target: { hit: { kind: 'region', id: right }, containingRegion: host.root },
      fuel: 256,
    })

    expect(leftPlan.ok && leftPlan.step.at.sel.regions).toEqual([left])
    expect(rightPlan.ok && rightPlan.step.at.sel.regions).toEqual([right])
  })

  it('does not treat the shared positive container as either occurrence footprint', () => {
    const host = new DiagramBuilder()
    const left = host.cut(host.root)
    host.cut(left)
    const right = host.cut(host.root)
    host.cut(right)
    const diagram = host.build()

    expect(planArtifactDrop({
      artifact,
      diagram,
      context: completed,
      target: { hit: { kind: 'region', id: host.root }, containingRegion: host.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })
  })

  it('validates candidates without mutating the supplied diagram', () => {
    const before = JSON.stringify(artifact.goal.diagram)
    planArtifactDrop({
      artifact,
      diagram: artifact.goal.diagram,
      context: completed,
      target: { hit: { kind: 'region', id: artifactGoal.eliminations[0]! }, containingRegion: artifact.goal.diagram.root },
      fuel: 256,
    })
    expect(JSON.stringify(artifact.goal.diagram)).toBe(before)
  })
})
