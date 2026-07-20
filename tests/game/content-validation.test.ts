import { describe, expect, it } from 'vitest'
import { createHash } from 'node:crypto'
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { validateGameContent } from '../../scripts/validate-game-content'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { cutDepth } from '../../src/kernel/diagram'

type JsonRecord = Record<string, any>

const readJson = (path: string): JsonRecord => JSON.parse(readFileSync(path, 'utf8')) as JsonRecord
const writeJson = (path: string, value: unknown): void => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`)
const sha256 = (value: unknown): string => createHash('sha256')
  .update(JSON.stringify(value)).digest('hex')

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

  it('preserves every incumbent Seyric bundle while adding onboarding beside it', () => {
    const onboarding = new Set([
      'two-veils', 'four-veils', 'forked-veil', 'echoed-veil', 'empty-ring-release',
    ])
    const onboardingObligations = new Set([
      'bare-double-cut-elimination',
      'repeated-double-cut-order-practice',
      'negative-field-empty-fragment-erasure',
      'cut-form-supported-deiteration',
      'vacuous-ring-elimination',
    ])
    const incumbentRootIds = new Set([
      'single-mark-return',
      'shallow-edit-legality-contrast',
      'atomic-fragment-erasure',
      'atomic-content-insertion',
      'compound-copy-authority-contrast',
      'transfer-duplication-recognition',
      'atomic-double-cut-selection',
      'common-conjunction-factor-base',
      'common-disjunction-factor-base',
      'content-bearing-annulus-choice',
      'disjunction-over-conjunction-base',
      'i-dao',
      'conjunction-idempotence-introduction',
      'weakening-introduction',
      'two-mark-projection',
      'left-injection-introduction',
      'disjunction-idempotence-introduction',
      'atomic-conjunction-exchange',
      'disjunction-exchange-recognition',
      'conjunction-reassociation-recognition',
      'disjunction-reassociation-recognition',
      'i-c3',
      'i-cs',
      'i-al',
      'i-case2',
      'i-om',
      'i-aa',
      'i-ao',
      'sey-ctr-i01',
      'sey-dm-ec-i01',
      'sey-dm-fc-i01',
      'sey-red-i01',
      'sey-pei-i01',
      'weakening-injection-weave',
      'b3',
      'de-morgan-product-consumer',
      'de-morgan-sum-consumer',
      'double-cut-copy-license',
      'double-cut-insertion-workspace',
      'preserve-sole-structural-source',
      'r4',
      'r5',
      'recollect-shared-branch-context',
      'rm-c3',
    ])
    const progression = readJson(resolve(process.cwd(), 'content/progression/core.json'))
    const incumbentIds = progression.cultures[0].puzzles.filter(
      (id: string) => !onboarding.has(id),
    ) as string[]
    const incumbent = new Set(incumbentIds)
    const catalog = readJson(resolve(process.cwd(), 'content/catalog/cursebreaker.json'))
    const guidance = readJson(resolve(process.cwd(), 'content/guidance/cursebreaker.json'))
    const coverage = readJson(resolve(process.cwd(), 'content/coverage/seyric.json'))
    const incumbentCoreBytes = incumbentIds.map((id) => readFileSync(resolve(
      process.cwd(), `content/puzzles/${id}.json`,
    ), 'utf8'))
    const preservedBundle = {
      seyric: incumbentIds,
      catalog: catalog.artifacts.filter(({ puzzle }: JsonRecord) => incumbent.has(puzzle)),
      guidance: guidance.puzzles.filter(({ puzzle }: JsonRecord) => incumbent.has(puzzle)),
      obligations: coverage.obligations.filter(({ id }: JsonRecord) => !onboardingObligations.has(id)),
      coverage: coverage.puzzles.filter(({ puzzle }: JsonRecord) => incumbent.has(puzzle)),
      validations: incumbentIds.map((id) => readJson(resolve(
        process.cwd(), `content/validation/${id}.json`,
      ))),
    }
    const incumbentProgression = structuredClone(progression)
    incumbentProgression.cultures[0].gateway = 'single-mark-return'
    incumbentProgression.cultures[0].puzzles = incumbentIds
    incumbentProgression.placements = incumbentProgression.placements
      .filter(({ puzzle }: JsonRecord) => !onboarding.has(puzzle))
      .map((placement: JsonRecord) => incumbentRootIds.has(placement.puzzle)
        ? { ...placement, prerequisites: [] }
        : placement)

    expect(sha256(incumbentCoreBytes))
      .toBe('dd698fc6630b7f6f4fff4c19c31a38b92bbbf19bf7cec29bc3e4893f74d1e720')
    expect(sha256(incumbentProgression))
      .toBe('c31a2917cd915b6056cd49b17ee02a5ba6d71d009b3141a668cb05449e45b6c9')
    expect(sha256(preservedBundle))
      .toBe('b9694b69f7ed6a2f3ce4131f26912790b7e5029c5a2a0150364b3accd7cd8083')
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
