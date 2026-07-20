import { describe, expect, it } from 'vitest'
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { findEmptyCutShortcutHosts, validateGameContent } from '../../scripts/validate-game-content'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { cutDepth } from '../../src/kernel/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'

type JsonRecord = Record<string, any>

const readJson = (path: string): JsonRecord => JSON.parse(readFileSync(path, 'utf8')) as JsonRecord
const writeJson = (path: string, value: unknown): void => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`)

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
