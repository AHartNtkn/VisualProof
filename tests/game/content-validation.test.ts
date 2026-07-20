import { describe, expect, it } from 'vitest'
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { findEmptyCutShortcutHosts, validateGameContent } from '../../scripts/validate-game-content'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { cutDepth, type Diagram, type RegionId, type SubgraphSelection } from '../../src/kernel/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyStep } from '../../src/kernel/proof'

type JsonRecord = Record<string, any>

const readJson = (path: string): JsonRecord => JSON.parse(readFileSync(path, 'utf8')) as JsonRecord
const writeJson = (path: string, value: unknown): void => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`)
const proofContext = { theorems: new Map(), relations: new Map() }

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
