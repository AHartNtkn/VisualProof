import { describe, expect, it } from 'vitest'
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { findEmptyCutShortcutHosts, validateGameContent } from '../../scripts/validate-game-content'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { cutDepth, type Diagram, type RegionId, type SubgraphSelection } from '../../src/kernel/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { applyStep } from '../../src/kernel/proof'

type JsonRecord = Record<string, any>

const readJson = (path: string): JsonRecord => JSON.parse(readFileSync(path, 'utf8')) as JsonRecord
const writeJson = (path: string, value: unknown): void => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`)
const proofContext = { theorems: new Map(), relations: new Map() }

const compoundPrimaryRule = new Map([
  ['compound-copy-authority-contrast', 'iteration'],
  ['compound-double-cut-selection', 'doubleCutIntro'],
  ['content-bearing-annulus-choice', 'doubleCutElim'],
  ['double-cut-insertion-workspace', 'insertion'],
])

const compoundPrerequisites = new Map([
  ['compound-copy-authority-contrast', ['marked-echo-deiteration']],
  ['compound-double-cut-selection', ['atomic-double-cut-selection']],
  ['content-bearing-annulus-choice', ['compound-double-cut-selection']],
  ['double-cut-insertion-workspace', ['atomic-double-cut-selection', 'atomic-content-insertion']],
])

const compoundPrimaryStepIndex = new Map([
  ['compound-copy-authority-contrast', 0],
  ['compound-double-cut-selection', 0],
  ['content-bearing-annulus-choice', 0],
  ['double-cut-insertion-workspace', 1],
])

const boundAtomPattern = (() => {
  const builder = new DiagramBuilder()
  const binder = builder.bubble(builder.root, 0)
  builder.atom(binder, binder)
  return { pattern: { diagram: builder.build(), boundary: [] }, binder }
})()

const insertBoundAtom = (
  diagram: Diagram,
  region: RegionId,
  binder: RegionId,
): Diagram => applyStep(diagram, {
  rule: 'insertion',
  region,
  pattern: boundAtomPattern.pattern,
  attachments: [],
  binders: { [boundAtomPattern.binder]: binder },
}, proofContext, 'backward')

const deiterate = (diagram: Diagram, sel: SubgraphSelection): Diagram => applyStep(diagram, {
  rule: 'deiteration', sel, fuel: 100,
}, proofContext, 'backward')

const contentBearingDoubleCutPatterns = (() => {
  const exactBuilder = new DiagramBuilder()
  const exactP = exactBuilder.bubble(exactBuilder.root, 0)
  const exactQ = exactBuilder.bubble(exactP, 0)
  const exactOuter = exactBuilder.cut(exactQ)
  const exactInner = exactBuilder.cut(exactOuter)
  exactBuilder.atom(exactInner, exactP)
  exactBuilder.atom(exactInner, exactQ)

  const nearbyBuilder = new DiagramBuilder()
  const nearbyP = nearbyBuilder.bubble(nearbyBuilder.root, 0)
  const nearbyOuter = nearbyBuilder.cut(nearbyP)
  const nearbyInner = nearbyBuilder.cut(nearbyOuter)
  nearbyBuilder.atom(nearbyInner, nearbyP)

  return {
    exact: {
      pattern: { diagram: exactBuilder.build(), boundary: [] },
      binders: { p: exactP, q: exactQ },
    },
    nearby: {
      pattern: { diagram: nearbyBuilder.build(), boundary: [] },
      binders: { p: nearbyP },
    },
  }
})()

const insertContentBearingDoubleCut = (
  diagram: Diagram,
  region: RegionId,
  binders: { readonly p: RegionId; readonly q?: RegionId },
): Diagram => {
  if (binders.q === undefined) {
    const source = contentBearingDoubleCutPatterns.nearby
    return applyStep(diagram, {
      rule: 'insertion',
      region,
      pattern: source.pattern,
      attachments: [],
      binders: { [source.binders.p]: binders.p },
    }, proofContext, 'backward')
  }
  const source = contentBearingDoubleCutPatterns.exact
  return applyStep(diagram, {
    rule: 'insertion',
    region,
    pattern: source.pattern,
    attachments: [],
    binders: {
      [source.binders.p]: binders.p,
      [source.binders.q]: binders.q,
    },
  }, proofContext, 'backward')
}

const innerCutAround = (diagram: Diagram, stableNode: string): SubgraphSelection => {
  const inner = diagram.nodes[stableNode]?.region
  if (inner === undefined) throw new Error(`missing stable node '${stableNode}'`)
  const innerRegion = diagram.regions[inner]
  if (innerRegion?.kind !== 'cut') throw new Error(`stable node '${stableNode}' is not inside a cut`)
  const outer = innerRegion.parent
  if (diagram.regions[outer]?.kind !== 'cut') {
    throw new Error(`stable node '${stableNode}' is not inside an introduced double cut`)
  }
  return { region: outer, regions: [inner], nodes: [], wires: [] }
}

const oneCleanupForms = (diagram: Diagram): ReadonlySet<string> => {
  const forms = new Set<string>()
  const record = (operation: () => Diagram): void => {
    try { forms.add(exploreForm(operation())) } catch { /* illegal candidate */ }
  }

  for (const region of Object.keys(diagram.regions)) {
    const childRegions = Object.entries(diagram.regions)
      .filter(([, candidate]) => candidate.kind !== 'sheet' && candidate.parent === region)
      .map(([id]) => id)
    const childNodes = Object.entries(diagram.nodes)
      .filter(([, node]) => node.region === region)
      .map(([id]) => id)
    const selectable = [
      ...childRegions.map((id) => ({ kind: 'region' as const, id })),
      ...childNodes.map((id) => ({ kind: 'node' as const, id })),
    ]
    for (let mask = 1; mask < 2 ** selectable.length; mask += 1) {
      const selected = selectable.filter((_, index) => (mask & (1 << index)) !== 0)
      const sel = {
        region,
        regions: selected.filter(({ kind }) => kind === 'region').map(({ id }) => id),
        nodes: selected.filter(({ kind }) => kind === 'node').map(({ id }) => id),
        wires: [],
      }
      record(() => deiterate(diagram, sel))
      record(() => applyStep(diagram, { rule: 'erasure', sel }, proofContext, 'backward'))
    }

    if (diagram.regions[region]?.kind === 'cut') {
      record(() => applyStep(diagram, {
        rule: 'doubleCutElim', region,
      }, proofContext, 'backward'))
    }
    if (diagram.regions[region]?.kind === 'bubble') {
      record(() => applyStep(diagram, {
        rule: 'vacuousElim', region,
      }, proofContext, 'backward'))
    }
  }
  return forms
}

const validateFixture = (mutate: (root: string) => void): void => {
  const root = mkdtempSync(join(tmpdir(), 'cursebreaker-content-validation-'))
  try {
    cpSync(resolve(process.cwd(), 'content'), root, { recursive: true })
    mutate(root)
    validateGameContent(root)
  } finally {
    rmSync(root, { recursive: true, force: true })
  }
}

describe('build-only game content evidence', () => {
  it('schema-validates every registered layer and replays every solution and recognized state', () => {
    const catalog = loadGameContent(gameContentFiles)
    const recognizedStates = catalog.puzzleIds.reduce(
      (count, id) => count + catalog.guidance(id).interventions.filter(
        ({ trigger }) => trigger.kind === 'recognizedUnwinnable',
      ).length,
      0,
    )

    expect(validateGameContent()).toEqual({
      puzzles: catalog.puzzleIds.length,
      solutions: catalog.puzzleIds.length,
      recognizedStates,
    })
  })

  it('gives the marked echo an ordinary deiteration-first witness', () => {
    const evidence = readJson(resolve(
      process.cwd(), 'content/validation/marked-echo-deiteration.json',
    ))
    expect(evidence.solution.map(({ rule }: JsonRecord) => rule)).toEqual([
      'deiteration', 'erasure', 'vacuousElim', 'doubleCutElim',
    ])
  })

  it('finds a negative host where an empty cut makes competing content disposable', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const owner = builder.bubble(outer, 0)
    builder.atom(owner, owner)
    builder.cut(owner)

    expect(findEmptyCutShortcutHosts(builder.build())).toEqual([owner])
  })

  it('does not flag an empty cut without competing content', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    builder.cut(outer)

    expect(findEmptyCutShortcutHosts(builder.build())).toEqual([])
  })

  it('does not flag a nonempty cut', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const owner = builder.bubble(outer, 0)
    const marked = builder.cut(owner)
    builder.atom(marked, owner)
    builder.atom(owner, owner)

    expect(findEmptyCutShortcutHosts(builder.build())).toEqual([])
  })

  it('keeps reconstructed atomic and polarity problems free of empty-cut truth witnesses', () => {
    const catalog = loadGameContent(gameContentFiles)
    const shortcutFree = [
      'shallow-edit-legality-contrast',
      'atomic-content-insertion',
      'atomic-double-cut-selection',
      'polarity-bubble-contrast',
    ] as const

    for (const id of shortcutFree) {
      expect(findEmptyCutShortcutHosts(catalog.puzzle(id as never).diagram), id).toEqual([])
    }
  })

  it('keeps reconstructed compound problems free of empty-cut truth witnesses', () => {
    const catalog = loadGameContent(gameContentFiles)

    for (const [id, primaryRule] of compoundPrimaryRule) {
      expect(findEmptyCutShortcutHosts(catalog.puzzle(id as never).diagram), id).toEqual([])
      const evidence = readJson(resolve(process.cwd(), `content/validation/${id}.json`))
      expect(evidence.solution[compoundPrimaryStepIndex.get(id)!]?.rule, id).toBe(primaryRule)
      expect(catalog.placement(id as never).prerequisites, id)
        .toEqual(compoundPrerequisites.get(id))
    }
  })

  it('uses a legal shallow insertion to unlock a pre-existing compound target', () => {
    const catalog = loadGameContent(gameContentFiles)
    const start = catalog.puzzle('shallow-edit-legality-contrast' as never).diagram
    const target = { region: 'r6', regions: [], nodes: ['n3', 'n4'], wires: [] }

    expect(() => insertBoundAtom(start, 'r3', 'r2')).toThrow(/requires a positive region/)
    expect(() => deiterate(start, target)).toThrow(/no justifying occurrence/)
    expect(() => deiterate(insertBoundAtom(start, 'r4', 'r2'), target)).not.toThrow()
    expect(() => deiterate(insertBoundAtom(start, 'r4', 'r3'), target))
      .toThrow(/no justifying occurrence/)
  })

  it('uses inserted atomic content as the exact source for a pre-existing branch', () => {
    const catalog = loadGameContent(gameContentFiles)
    const start = catalog.puzzle('atomic-content-insertion' as never).diagram
    const target = { region: 'r5', regions: ['r6'], nodes: [], wires: [] }

    expect(() => deiterate(start, target)).toThrow(/no justifying occurrence/)
    expect(() => deiterate(insertBoundAtom(start, 'r4', 'r3'), target)).not.toThrow()
    expect(() => deiterate(insertBoundAtom(start, 'r4', 'r2'), target))
      .toThrow(/no justifying occurrence/)
  })

  it('uses only the exact atomic double cut to create deiteration authority', () => {
    const catalog = loadGameContent(gameContentFiles)
    const start = catalog.puzzle('atomic-double-cut-selection' as never).diagram

    expect(() => deiterate(start, {
      region: 'r5', regions: [], nodes: ['n1'], wires: [],
    })).toThrow(/no justifying occurrence/)

    const exact = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r5', regions: [], nodes: ['n1'], wires: [] },
    }, proofContext, 'backward')
    expect(() => deiterate(exact, innerCutAround(exact, 'n1'))).not.toThrow()

    const nearby = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r6', regions: [], nodes: ['n2'], wires: [] },
    }, proofContext, 'backward')
    expect(() => deiterate(nearby, innerCutAround(nearby, 'n2')))
      .toThrow(/no justifying occurrence/)

    const larger = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r5', regions: ['r6'], nodes: ['n1'], wires: [] },
    }, proofContext, 'backward')
    expect(() => deiterate(larger, innerCutAround(larger, 'n1')))
      .toThrow(/no justifying occurrence/)
  })

  it('uses descendant authority to make a copied compound material', () => {
    const start = loadGameContent(gameContentFiles)
      .puzzle('compound-copy-authority-contrast' as never).diagram
    const source = { region: 'r6', regions: [], nodes: ['n1', 'n2'], wires: [] }
    const target = { region: 'r7', regions: [], nodes: ['n4', 'n5', 'n6'], wires: [] }

    expect(() => deiterate(start, target)).toThrow(/no justifying occurrence/)
    const copied = applyStep(start, {
      rule: 'iteration', sel: source, target: 'r7',
    }, proofContext, 'backward')
    expect(() => deiterate(copied, target)).not.toThrow()

    const partial = applyStep(start, {
      rule: 'iteration',
      sel: { region: 'r6', regions: [], nodes: ['n1'], wires: [] },
      target: 'r7',
    }, proofContext, 'backward')
    expect(() => deiterate(partial, target)).toThrow(/no justifying occurrence/)

    for (const sameRegionSource of [source, {
      region: 'r6', regions: [], nodes: ['n1'], wires: [],
    }]) {
      const sameRegion = applyStep(start, {
        rule: 'iteration', sel: sameRegionSource, target: 'r6',
      }, proofContext, 'backward')
      expect(() => deiterate(sameRegion, target)).toThrow(/no justifying occurrence/)
    }

    expect(() => applyStep(start, {
      rule: 'iteration', sel: source, target: 'r8',
    }, proofContext, 'backward')).toThrow(/must lie within the source region/)
  })

  it('uses only the intact compound double cut to create deiteration authority', () => {
    const start = loadGameContent(gameContentFiles)
      .puzzle('compound-double-cut-selection' as never).diagram

    expect(() => deiterate(start, {
      region: 'r6', regions: [], nodes: ['n2', 'n3'], wires: [],
    })).toThrow(/no justifying occurrence/)

    const exact = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r6', regions: [], nodes: ['n2', 'n3'], wires: [] },
    }, proofContext, 'backward')
    const exactPost = deiterate(exact, innerCutAround(exact, 'n2'))

    const nearby = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r6', regions: [], nodes: ['n2'], wires: [] },
    }, proofContext, 'backward')
    expect(() => deiterate(nearby, innerCutAround(nearby, 'n2')))
      .toThrow(/no justifying occurrence/)
    expect(oneCleanupForms(nearby)).not.toContain(exploreForm(exactPost))

    const larger = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r6', regions: [], nodes: ['n2', 'n3', 'n4'], wires: [] },
    }, proofContext, 'backward')
    expect(() => deiterate(larger, innerCutAround(larger, 'n2')))
      .toThrow(/no justifying occurrence/)
    expect(oneCleanupForms(larger)).not.toContain(exploreForm(exactPost))
  })

  it('preserves the selected annulus content for a later exact transition', () => {
    const start = loadGameContent(gameContentFiles)
      .puzzle('content-bearing-annulus-choice' as never).diagram
    const consumed = { region: 'r4', regions: [], nodes: ['n3', 'n4', 'n5'], wires: [] }

    expect(start.nodes.n4?.region).toBe('r6')
    expect(start.nodes.n5?.region).toBe('r6')
    const selected = applyStep(start, {
      rule: 'doubleCutElim', region: 'r5',
    }, proofContext, 'backward')
    expect(selected.nodes.n4?.region).toBe('r4')
    expect(selected.nodes.n5?.region).toBe('r4')
    expect(() => deiterate(selected, consumed)).not.toThrow()

    expect(() => applyStep(start, {
      rule: 'doubleCutElim', region: 'r7',
    }, proofContext, 'backward')).toThrow(/annulus.*must contain exactly one child cut and nothing else/)
  })

  it('uses the introduced positive annulus for a material compound insertion', () => {
    const start = loadGameContent(gameContentFiles)
      .puzzle('double-cut-insertion-workspace' as never).diagram
    const preIntroTarget = { region: 'r3', regions: ['r4'], nodes: [], wires: [] }

    expect(() => insertContentBearingDoubleCut(start, 'r3', { p: 'r2', q: 'r3' }))
      .toThrow(/requires a positive region/)
    for (const existingPositiveHost of ['r4', 'r6']) {
      const direct = insertContentBearingDoubleCut(start, existingPositiveHost, {
        p: 'r2', q: 'r3',
      })
      expect(() => deiterate(direct, preIntroTarget)).toThrow(/no justifying occurrence/)
    }
    const introduced = applyStep(start, {
      rule: 'doubleCutIntro',
      sel: { region: 'r3', regions: ['r4'], nodes: [], wires: [] },
    }, proofContext, 'backward')
    const target = { region: 'dc_0', regions: ['r4'], nodes: [], wires: [] }
    expect(() => deiterate(introduced, target)).toThrow(/no justifying occurrence/)

    const inserted = insertContentBearingDoubleCut(introduced, 'dc', { p: 'r2', q: 'r3' })
    expect(() => deiterate(inserted, target)).not.toThrow()

    const nearby = insertContentBearingDoubleCut(introduced, 'dc', { p: 'r2' })
    expect(() => deiterate(nearby, target)).toThrow(/no justifying occurrence/)
    expect(() => insertContentBearingDoubleCut(introduced, 'dc_0', { p: 'r2', q: 'r3' }))
      .toThrow(/requires a positive region/)
  })

  it('represents both nested owners as distinct binder pairs', () => {
    const diagram = loadGameContent(gameContentFiles).puzzle('nested-owner-introduction' as never).diagram
    const binders = ['n0', 'n1', 'n2', 'n3'].map((id) => diagram.nodes[id]).map((node) => {
      expect(node?.kind).toBe('atom')
      return node?.kind === 'atom' ? node.binder : undefined
    })

    expect(binders).toEqual(['r2', 'r3', 'r2', 'r3'])
    expect(new Set(binders).size).toBe(2)
  })

  it('gives every implemented Seyric puzzle a distinct logical starting problem', () => {
    const catalog = loadGameContent(gameContentFiles)
    const byFingerprint = new Map<string, string[]>()
    for (const id of catalog.puzzlesInCulture('seyric-horizon' as never)) {
      const fingerprint = catalog.puzzleFingerprint(id)
      byFingerprint.set(fingerprint, [...(byFingerprint.get(fingerprint) ?? []), id])
    }

    expect([...byFingerprint.values()].filter((ids) => ids.length > 1)).toEqual([])
  })

  it('rejects a Seyric puzzle with no coverage row', () => {
    expect(() => validateFixture((root) => {
      const path = join(root, 'coverage/seyric.json')
      const coverage = readJson(path)
      coverage.puzzles = coverage.puzzles.filter(({ puzzle }: JsonRecord) => puzzle !== 'single-mark-return')
      writeJson(path, coverage)
    })).toThrow(/no coverage row/)
  })

  it('rejects duplicate canonical Seyric starts', () => {
    expect(() => validateFixture((root) => {
      const manifest = readJson(join(root, 'manifest.json'))
      const firstPath = manifest.puzzles[0] as string
      const secondPath = manifest.puzzles[1] as string
      const first = readJson(join(root, firstPath))
      const second = readJson(join(root, secondPath))
      second.diagram = first.diagram
      writeJson(join(root, secondPath), second)
    })).toThrow(/duplicate canonical start/)
  })

  it('rejects the obsolete placement optionality field', () => {
    expect(() => validateFixture((root) => {
      const path = join(root, 'progression/core.json')
      const progression = readJson(path)
      progression.placements[0].optional = false
      writeJson(path, progression)
    })).toThrow(/additional properties|unknown field.*optional/i)
  })

  it('rejects coverage that names an unknown obligation', () => {
    expect(() => validateFixture((root) => {
      const path = join(root, 'coverage/seyric.json')
      const coverage = readJson(path)
      coverage.puzzles[0].obligations.push('unknown-obligation')
      writeJson(path, coverage)
    })).toThrow(/unknown obligation/)
  })

  it('rejects a retained Seyric puzzle with no obligation', () => {
    expect(() => validateFixture((root) => {
      const path = join(root, 'coverage/seyric.json')
      const coverage = readJson(path)
      coverage.puzzles[1].obligations.push(...coverage.puzzles[0].obligations)
      coverage.puzzles[0].obligations = []
      writeJson(path, coverage)
    })).toThrow(/at least one obligation|must NOT have fewer than 1 items/)
  })

  it('rejects an uncovered obligation', () => {
    expect(() => validateFixture((root) => {
      const path = join(root, 'coverage/seyric.json')
      const coverage = readJson(path)
      coverage.obligations.push({
        id: 'deliberately-uncovered', kind: 'isolated', family: 'test-only',
        distinction: 'A deliberately uncovered distinction.',
        stoppingRule: 'Exists only to prove direct coverage validation.',
      })
      writeJson(path, coverage)
    })).toThrow(/uncovered obligation/)
  })

  it('keeps every implemented Seyric problem inside the propositional culture boundary', () => {
    const catalog = loadGameContent(gameContentFiles)
    const violations: string[] = []
    for (const id of catalog.puzzlesInCulture('seyric-horizon' as never)) {
      const diagram = catalog.puzzle(id).diagram
      for (const [regionId, region] of Object.entries(diagram.regions)) {
        if (region.kind !== 'bubble') continue
        if (region.arity !== 0) violations.push(`${id}: bubble '${regionId}' has arity ${region.arity}`)
        if (cutDepth(diagram, regionId) % 2 === 0) violations.push(`${id}: bubble '${regionId}' is existential`)
      }
      for (const [nodeId, node] of Object.entries(diagram.nodes)) {
        if (node.kind !== 'atom') violations.push(`${id}: node '${nodeId}' has kind '${node.kind}'`)
      }
      if (Object.keys(diagram.wires).length > 0) violations.push(`${id}: contains individual wires`)
    }

    expect(violations).toEqual([])
  })

})
