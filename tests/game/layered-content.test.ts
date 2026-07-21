import { describe, expect, it } from 'vitest'
import * as catalogModule from '../../src/game/catalog'
import * as contentModule from '../../src/game/content'
import { diagramToJson } from '../../src/kernel/diagram/json'
import { artifactTheoremContext, artifactTheoremName } from '../../src/game/artifact-theorem'
import { twoVeils } from './fixtures'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'

const portableFiles = (overrides: Record<string, unknown> = {}): Record<string, unknown> => {
  const diagram = diagramToJson(twoVeils().goal.diagram)
  return {
    'manifest.json': {
      format: 'cursebreaker-content', version: 3,
      puzzles: ['puzzles/two-veils.json'], definitions: [],
      progression: 'progression/core.json',
      coverage: { 'seyric-horizon': 'coverage/seyric.json' },
      catalog: 'catalog/cursebreaker.json',
      guidance: 'guidance/cursebreaker.json',
    },
    'puzzles/two-veils.json': { id: 'two-veils', diagram },
    'progression/core.json': {
      cultures: [{
        id: 'seyric-horizon', order: 0, unlocksAfter: [], gateway: 'two-veils',
        puzzles: ['two-veils'],
      }],
      placements: [{
        puzzle: 'two-veils', prerequisites: [],
      }],
    },
    'coverage/seyric.json': {
      obligations: [{
        id: 'paired-veils', kind: 'isolated', family: 'double-cut',
        distinction: 'Release paired veils.', stoppingRule: 'Stop after one pair.',
      }],
      puzzles: [{
        puzzle: 'two-veils', obligations: ['paired-veils'],
        visibleSituation: 'A nested pair of empty veils.',
        defeats: 'The two boundaries move together.', experientialNeighbors: [],
      }],
    },
    'catalog/cursebreaker.json': {
      cultures: [{
        id: 'seyric-horizon', name: 'The Seyric Horizon', shortName: 'Seyric',
        relativeAge: 0, historicalSummary: 'The earliest secure sealing horizon.',
        lineage: [], isolation: 'uncertain', sealingVocabulary: ['veils'],
      }],
      artifacts: [{
        puzzle: 'two-veils', name: { professional: 'The Seyr Ossuary Seal' },
        provenance: { summary: 'A basalt stopper.', function: 'Contained a curse.' },
      }],
    },
    'guidance/cursebreaker.json': {
      puzzles: [{
        puzzle: 'two-veils', interventions: [{
          id: 'opening-paired-veils',
          trigger: { kind: 'opening' }, repeat: 'once', pages: ['Select the paired veils.'],
        }],
      }],
    },
    ...overrides,
  }
}

describe('layered portable game content', () => {
  it('exposes one decoder and assembler for portable content files', () => {
    expect(typeof (catalogModule as Record<string, unknown>).loadGameContent).toBe('function')
  })

  it('assembles independent immutable layers around a minimal semantic puzzle', () => {
    const catalog = catalogModule.loadGameContent(portableFiles()) as never as {
      puzzleIds: readonly string[]
      cultureIds: readonly string[]
      puzzle(id: string): { id: string; diagram: unknown }
      placement(id: string): {
        puzzle: string
        culture: string
        prerequisites: readonly string[]
      }
      artifact(id: string): { puzzle: string; name: { professional: string } }
      guidance(id: string): { puzzle: string; interventions: readonly unknown[] }
      puzzlesInCulture(id: string): readonly string[]
      source?: unknown
    }

    expect(catalog.puzzleIds).toEqual(['two-veils'])
    expect(catalog.cultureIds).toEqual(['seyric-horizon'])
    expect(Object.keys(catalog.puzzle('two-veils')).sort()).toEqual(['diagram', 'id'])
    expect(catalog.placement('two-veils')).toEqual({
      puzzle: 'two-veils', culture: 'seyric-horizon', prerequisites: [],
    })
    expect(catalog.artifact('two-veils').name.professional).toBe('The Seyr Ossuary Seal')
    expect(catalog.guidance('two-veils').interventions).toHaveLength(1)
    expect(catalog.puzzlesInCulture('seyric-horizon')).toEqual(['two-veils'])
    expect(catalog.source).toBeUndefined()
    expect(() => (catalog.puzzleIds as string[]).push('intruder')).toThrow()
  })

  it('rejects engine, overlay, and validation concerns in a core puzzle record', () => {
    const base = portableFiles()
    const puzzle = base['puzzles/two-veils.json'] as Record<string, unknown>
    for (const forbidden of ['witness', 'teacher', 'prerequisites', 'presentation', 'completion']) {
      expect(() => catalogModule.loadGameContent(portableFiles({
        'puzzles/two-veils.json': { ...puzzle, [forbidden]: [] },
      }))).toThrow(/unknown field/)
    }
  })

  it('rejects displaced curriculum and performance ownership', () => {
    const files = portableFiles()
    const manifest = files['manifest.json'] as Record<string, unknown>
    expect(() => catalogModule.loadGameContent({
      ...files,
      'manifest.json': { ...manifest, version: 2 },
    })).toThrow(/version must be 3/)

    expect(() => catalogModule.loadGameContent({
      ...files,
      'manifest.json': {
        ...manifest,
        version: 1,
        curriculum: 'curriculum/core.json',
      },
    })).toThrow(/version must be 3|unknown field 'curriculum'/)

    const progression = files['progression/core.json'] as { placements: Array<Record<string, unknown>> }
    expect(() => catalogModule.loadGameContent({
      ...files,
      'progression/core.json': { ...progression, performances: [] },
    })).toThrow(/unknown field 'performances'/)

    expect(() => catalogModule.loadGameContent({
      ...files,
      'progression/core.json': {
        ...progression,
        placements: progression.placements.map((placement) => ({
          ...placement,
          learning: { introduces: ['release-paired-veils'] },
        })),
      },
    })).toThrow(/unknown field 'learning'/)

    expect(() => catalogModule.loadGameContent({
      ...files,
      'progression/core.json': {
        ...progression,
        placements: progression.placements.map((placement) => ({
          ...placement,
          optional: false,
        })),
      },
    })).toThrow(/unknown field 'optional'/)

    const guidance = files['guidance/cursebreaker.json'] as {
      puzzles: Array<{ interventions: Array<Record<string, unknown>> }>
    }
    guidance.puzzles[0]!.interventions[0]!.performance = 'release-paired-veils'
    expect(() => catalogModule.loadGameContent(files)).toThrow(/unknown field 'performance'/)
  })

  it('validates culture-owned coverage paths without importing build-only payloads', () => {
    const files = portableFiles()
    const manifest = files['manifest.json'] as Record<string, unknown>
    expect(() => catalogModule.loadGameContent({
      ...files,
      'manifest.json': {
        ...manifest,
        coverage: { 'other-culture': 'coverage/seyric.json' },
      },
    })).toThrow(/coverage cultures must match catalog cultures exactly/)

    const { ['coverage/seyric.json']: _missing, ...withoutCoverage } = files
    expect(() => catalogModule.loadGameContent(withoutCoverage)).not.toThrow()
  })

  it('rejects missing layer ownership, cyclic progression, and non-authored hint triggers', () => {
    const missingArtifact = portableFiles()
    const catalog = missingArtifact['catalog/cursebreaker.json'] as { cultures: unknown[]; artifacts: unknown[] }
    expect(() => catalogModule.loadGameContent({
      ...missingArtifact,
      'catalog/cursebreaker.json': { ...catalog, artifacts: [] },
    })).toThrow(/no catalog artifact/)

    const cyclic = portableFiles()
    const progression = cyclic['progression/core.json'] as {
      cultures: unknown[]; placements: Array<Record<string, unknown>>
    }
    expect(() => catalogModule.loadGameContent({
      ...cyclic,
      'progression/core.json': {
        ...progression,
        placements: progression.placements.map((placement) => ({
          ...placement, prerequisites: ['two-veils'],
        })),
      },
    })).toThrow(/dependency cycle/)

    const hinted = portableFiles()
    const guidance = hinted['guidance/cursebreaker.json'] as {
      puzzles: Array<{ puzzle: string; interventions: Array<Record<string, unknown>> }>
    }
    guidance.puzzles[0]!.interventions[0]!.trigger = { kind: 'stalled' }
    expect(() => catalogModule.loadGameContent(hinted)).toThrow(/trigger kind is invalid/)
  })

  it('fingerprints only canonical puzzle semantics and referenced definitions', () => {
    const original = catalogModule.loadGameContent(portableFiles()) as never as {
      puzzleFingerprint(id: string): string
    }
    const changedCatalog = portableFiles()
    const catalog = changedCatalog['catalog/cursebreaker.json'] as {
      cultures: unknown[]; artifacts: Array<Record<string, unknown>>
    }
    const changed = catalogModule.loadGameContent({
      ...changedCatalog,
      'catalog/cursebreaker.json': {
        ...catalog,
        artifacts: catalog.artifacts.map((artifact) => ({
          ...artifact, name: { professional: 'A newly catalogued name' },
        })),
      },
    }) as never as { puzzleFingerprint(id: string): string }

    expect(original.puzzleFingerprint('two-veils')).toBe(changed.puzzleFingerprint('two-veils'))
    expect(original.puzzleFingerprint('two-veils')).toContain('diagram')
    expect(original.puzzleFingerprint('two-veils')).not.toMatch(/^[0-9a-f]{8}$/)
  })

  it('loads production through manifest v3 with culture-owned coverage', () => {
    const files = (contentModule as Record<string, unknown>).gameContentFiles
    expect(files).toBeTypeOf('object')
    const manifest = (files as Record<string, unknown>)['manifest.json']
    expect(manifest).toEqual({
      format: 'cursebreaker-content',
      version: 3,
      puzzles: expect.any(Array),
      definitions: expect.any(Array),
      progression: 'progression/core.json',
      coverage: {
        'seyric-horizon': 'coverage/seyric.json',
        'myratic-tradition': 'coverage/myratic.json',
      },
      catalog: 'catalog/cursebreaker.json',
      guidance: 'guidance/cursebreaker.json',
    })
    expect(files).not.toHaveProperty('coverage/seyric.json')
    expect(files).not.toHaveProperty('coverage/myratic.json')

    const catalog = catalogModule.loadGameContent(files as Record<string, unknown>)

    expect(catalog.puzzleIds).toEqual(
      catalog.cultureIds.flatMap((culture) => catalog.puzzlesInCulture(culture)),
    )
    const seyric = catalog.puzzlesInCulture('seyric-horizon' as never)
    expect(seyric.indexOf('single-mark-return' as never))
      .toBeLessThan(seyric.indexOf('marked-echo-deiteration' as never))
    for (const [earlier, later] of [
      ['seyric-atomic-double-cut-selection', 'compound-double-cut-selection'],
      ['two-mark-projection', 'compound-projection'],
      ['left-injection-introduction', 'disjunction-idempotence-introduction'],
      ['atomic-conjunction-exchange', 'conjunction-reassociation-recognition'],
      ['disjunction-exchange-recognition', 'disjunction-reassociation-recognition'],
      ['disjunction-reassociation-recognition', 'structural-recognition-routing-choice'],
    ] as const) {
      expect(seyric.indexOf(earlier as never)).toBeLessThan(seyric.indexOf(later as never))
    }

    for (const [id, prerequisites] of [
      ['seyric-field-edit-contrast', ['nested-owner-introduction']],
      ['seyric-compound-copy-authority', ['marked-echo-deiteration']],
      ['seyric-atomic-double-cut-selection', ['marked-echo-deiteration']],
      ['seyric-extraction-continuation', ['nested-owner-introduction']],
      ['compound-double-cut-selection', ['seyric-atomic-double-cut-selection']],
      ['compound-weakening-boundary', ['two-mark-projection']],
      ['compound-projection', ['two-mark-projection']],
      [
        'structural-recognition-routing-choice',
        ['conjunction-reassociation-recognition', 'disjunction-reassociation-recognition'],
      ],
    ] as const) {
      expect(catalog.placement(id as never)).toEqual({
        puzzle: id,
        culture: 'seyric-horizon',
        prerequisites,
      })
    }

    expect(catalog.culture('myratic-tradition' as never)).toMatchObject({
      gateway: 'blank-witness',
      unlocksAfter: ['nested-owner-introduction'],
      puzzles: expect.arrayContaining([
        'blank-witness',
        'artifact-selected-downstream-bridge',
      ]),
    })
    expect(catalog.placement('artifact-selected-downstream-bridge' as never)).toEqual({
      puzzle: 'artifact-selected-downstream-bridge',
      culture: 'myratic-tradition',
      prerequisites: ['blank-witness', 'i-c3', 'i-c4'],
    })
  })

  it('constructs completed artifact theorems without runtime witnesses', () => {
    const catalog = catalogModule.loadGameContent(portableFiles())
    const id = catalog.puzzleIds[0]!
    const context = artifactTheoremContext(catalog as never, new Set([id]))
    const theorem = context.theorems.get(artifactTheoremName(id))
    expect(theorem).toMatchObject({ steps: [], backSteps: [] })
    expect(theorem?.rhs.diagram).toBe(catalog.puzzle(id).diagram)
  })

  it('tracks only transitively referenced definition semantics, independent of definition names', () => {
    const puzzleBuilder = new DiagramBuilder()
    puzzleBuilder.ref(puzzleBuilder.root, 'alpha', 0)
    const alphaBuilder = new DiagramBuilder()
    alphaBuilder.ref(alphaBuilder.root, 'beta', 0)
    const betaBuilder = new DiagramBuilder()
    const outer = betaBuilder.cut(betaBuilder.root)
    betaBuilder.cut(outer)
    const unrelatedBuilder = new DiagramBuilder()

    const withDefinitions = (alpha: string, beta: string, betaDiagram: unknown, unrelatedDiagram: unknown) => {
      const files = portableFiles()
      const manifest = files['manifest.json'] as Record<string, unknown>
      return {
        ...files,
        'manifest.json': {
          ...manifest,
          definitions: [`definitions/${alpha}.json`, `definitions/${beta}.json`, 'definitions/unrelated.json'],
        },
        'puzzles/two-veils.json': { id: 'two-veils', diagram: {
          ...diagramToJson(puzzleBuilder.build()) as Record<string, unknown>,
          nodes: { n0: { kind: 'ref', region: 'r0', defId: alpha, arity: 0 } },
        } },
        [`definitions/${alpha}.json`]: { id: alpha, diagram: {
          ...diagramToJson(alphaBuilder.build()) as Record<string, unknown>,
          nodes: { n0: { kind: 'ref', region: 'r0', defId: beta, arity: 0 } },
        }, boundary: [] },
        [`definitions/${beta}.json`]: { id: beta, diagram: betaDiagram, boundary: [] },
        'definitions/unrelated.json': { id: 'unrelated', diagram: unrelatedDiagram, boundary: [] },
      }
    }
    const base = withDefinitions('alpha', 'beta', diagramToJson(betaBuilder.build()), diagramToJson(unrelatedBuilder.build()))
    const renamed = withDefinitions('renamed-alpha', 'renamed-beta', diagramToJson(betaBuilder.build()), diagramToJson(twoVeils().goal.diagram))
    const changedBeta = new DiagramBuilder()
    const first = changedBeta.cut(changedBeta.root)
    const second = changedBeta.cut(first)
    const third = changedBeta.cut(second)
    changedBeta.cut(third)

    const originalFingerprint = catalogModule.loadGameContent(base).puzzleFingerprint('two-veils' as never)
    expect(catalogModule.loadGameContent(renamed).puzzleFingerprint('two-veils' as never)).toBe(originalFingerprint)
    expect(catalogModule.loadGameContent(withDefinitions(
      'alpha', 'beta', diagramToJson(changedBeta.build()), diagramToJson(unrelatedBuilder.build()),
    )).puzzleFingerprint('two-veils' as never)).not.toBe(originalFingerprint)
  })
})
