import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyArtifactAction } from '../../src/game/artifact'
import { planArtifactDrop } from '../../src/game/interface/artifact-drop'
import { buildTestCatalog, minimalPuzzle, minimalSource } from './catalog-fixture'
import { twoVeils } from './fixtures'

const artifactGoal = twoVeils()
const testArtifact = minimalPuzzle({ goal: artifactGoal.goal })
const source = minimalSource()
const catalog = buildTestCatalog({
  ...source,
  cultures: [{ ...source.cultures[0]!, gateway: testArtifact.id }],
  puzzles: [testArtifact],
})
const artifact = catalog.puzzle(testArtifact.id)

describe('completed artifact drop authority', () => {
  it('dissolves a cut-only exact occurrence through a game-owned artifact action', () => {
    const result = planArtifactDrop({
      artifact,
      available: true,
      diagram: artifact.diagram,
      target: {
        hit: { kind: 'region', id: artifactGoal.eliminations[0]! },
        containingRegion: artifact.diagram.root,
      },
      fuel: 256,
    })

    expect(result).toMatchObject({
      ok: true,
      operation: 'dissolve',
      action: { kind: 'artifactDissolve', artifact: artifact.id },
    })
    if (!result.ok) throw new Error(result.reason)
    expect(Object.keys(applyArtifactAction(artifact.diagram, result.action, artifact).regions))
      .toEqual([artifact.diagram.root])
  })

  it('manifests into the actual smallest negative containing region', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const diagram = host.build()
    const result = planArtifactDrop({
      artifact,
      available: true,
      diagram,
      target: { hit: { kind: 'region', id: negative }, containingRegion: negative },
      fuel: 256,
    })

    expect(result).toMatchObject({
      ok: true,
      operation: 'manifest',
      action: { kind: 'artifactManifest', artifact: artifact.id, region: negative },
    })
    if (!result.ok) throw new Error(result.reason)
    expect(Object.values(applyArtifactAction(diagram, result.action, artifact).regions)
      .filter((region) => region.kind === 'cut')).toHaveLength(3)
  })

  it('refuses incomplete artifacts, similar forms, and strict-subgraph hits without an action', () => {
    expect(planArtifactDrop({
      artifact,
      available: false,
      diagram: artifact.diagram,
      target: { hit: { kind: 'region', id: artifactGoal.eliminations[0]! }, containingRegion: artifact.diagram.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'artifact-incomplete' })

    const similar = new DiagramBuilder()
    const onlyCut = similar.cut(similar.root)
    const similarDiagram = similar.build()
    expect(planArtifactDrop({
      artifact,
      available: true,
      diagram: similarDiagram,
      target: { hit: { kind: 'region', id: onlyCut }, containingRegion: similar.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })

    expect(planArtifactDrop({
      artifact,
      available: true,
      diagram: artifact.diagram,
      target: { hit: null, containingRegion: artifact.diagram.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })
  })

  it('refuses an outside-canvas target before matching or insertion', () => {
    expect(planArtifactDrop({
      artifact,
      available: true,
      diagram: artifact.diagram,
      target: { hit: null, containingRegion: null },
      fuel: 256,
    })).toEqual({
      ok: false,
      code: 'invalid-drop-target',
      reason: 'the dropped artifact is outside the active seal',
    })
  })

  it('does not turn a substantive wrong hit into manifestation in an otherwise eligible field', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const wrongNode = host.termNode(negative, parseTerm('x'))
    const diagram = host.build()

    expect(planArtifactDrop({
      artifact,
      available: true,
      diagram,
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
      available: true,
      diagram,
      target: { hit: { kind: 'region', id: left }, containingRegion: host.root },
      fuel: 256,
    })
    const rightPlan = planArtifactDrop({
      artifact,
      available: true,
      diagram,
      target: { hit: { kind: 'region', id: right }, containingRegion: host.root },
      fuel: 256,
    })

    expect(leftPlan.ok && leftPlan.action.kind === 'artifactDissolve'
      && leftPlan.action.selection.regions).toEqual([left])
    expect(rightPlan.ok && rightPlan.action.kind === 'artifactDissolve'
      && rightPlan.action.selection.regions).toEqual([right])
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
      available: true,
      diagram,
      target: { hit: { kind: 'region', id: host.root }, containingRegion: host.root },
      fuel: 256,
    })).toMatchObject({ ok: false, code: 'no-legal-artifact-operation' })
  })

  it('plans candidates without mutating the supplied diagram', () => {
    const before = JSON.stringify(artifact.diagram)
    planArtifactDrop({
      artifact,
      available: true,
      diagram: artifact.diagram,
      target: { hit: { kind: 'region', id: artifactGoal.eliminations[0]! }, containingRegion: artifact.diagram.root },
      fuel: 256,
    })
    expect(JSON.stringify(artifact.diagram)).toBe(before)
  })
})
