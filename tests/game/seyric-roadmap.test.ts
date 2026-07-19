import { describe, expect, it } from 'vitest'
import roadmapJson from '../../content/roadmaps/seyric.json'

type Stage = 'structural' | 'connective' | 'classical'
type Role =
  | 'introduction' | 'contrast' | 'application' | 'retrieval'
  | 'mixed' | 'transfer' | 'remediation' | 'challenge'
type Skill = {
  readonly id: string
  readonly label: string
  readonly stage: Stage
  readonly mode: 'move' | 'recognition' | 'interface'
  readonly prerequisites: readonly string[]
}
type Evidence = { readonly skill: string; readonly role: Role; readonly primary?: boolean }
type Puzzle = {
  readonly id: string
  readonly stage: Stage
  readonly folioOrder: number
  readonly prerequisites: readonly string[]
  readonly evidence: readonly [Evidence, ...Evidence[]]
  readonly sourceLabels: readonly string[]
}
type Roadmap = {
  readonly format: 'cursebreaker-seyric-roadmap'
  readonly version: 1
  readonly finalTransfer: string
  readonly stages: readonly { readonly id: Stage; readonly order: number }[]
  readonly skills: readonly Skill[]
  readonly puzzles: readonly Puzzle[]
  readonly internalLabels: readonly { readonly label: string; readonly puzzle: string; readonly reason: string }[]
}

const roadmap = roadmapJson as unknown as Roadmap
const unique = (values: readonly string[]): boolean => new Set(values).size === values.length

const findCycle = (nodes: readonly { readonly id: string; readonly prerequisites: readonly string[] }[]): readonly string[] | null => {
  const prerequisites = new Map(nodes.map(({ id, prerequisites }) => [id, prerequisites] as const))
  const visited = new Set<string>()
  const visiting = new Set<string>()
  const path: string[] = []
  const visit = (id: string): readonly string[] | null => {
    if (visiting.has(id)) return [...path.slice(path.indexOf(id)), id]
    if (visited.has(id)) return null
    visiting.add(id)
    path.push(id)
    for (const parent of prerequisites.get(id) ?? []) {
      const cycle = visit(parent)
      if (cycle !== null) return cycle
    }
    path.pop()
    visiting.delete(id)
    visited.add(id)
    return null
  }
  for (const { id } of nodes) {
    const cycle = visit(id)
    if (cycle !== null) return cycle
  }
  return null
}

type SkillEvidence = { readonly puzzle: string; readonly role: Role }
const evidenceBySkill = (puzzles: readonly Puzzle[]): ReadonlyMap<string, readonly SkillEvidence[]> => {
  const out = new Map<string, SkillEvidence[]>()
  for (const puzzle of puzzles) {
    for (const evidence of puzzle.evidence) {
      const rows = out.get(evidence.skill) ?? []
      rows.push({ puzzle: puzzle.id, role: evidence.role })
      out.set(evidence.skill, rows)
    }
  }
  return out
}
const idsFor = (rows: readonly SkillEvidence[], role: Role): readonly string[] =>
  [...new Set(rows.filter((row) => row.role === role).map(({ puzzle }) => puzzle))]

const prerequisiteClosure = (target: string, puzzles: readonly Puzzle[]): ReadonlySet<string> => {
  const byId = new Map(puzzles.map((puzzle) => [puzzle.id, puzzle] as const))
  const closure = new Set<string>()
  const add = (id: string): void => {
    if (closure.has(id)) return
    const puzzle = byId.get(id)
    if (puzzle === undefined) throw new Error(`unknown puzzle '${id}'`)
    closure.add(id)
    for (const parent of puzzle.prerequisites) add(parent)
  }
  add(target)
  return closure
}

describe('normalized Seyric roadmap', () => {
  it('owns emitted identities without encoding target counts', () => {
    expect(roadmap.format).toBe('cursebreaker-seyric-roadmap')
    expect(roadmap.version).toBe(1)
    expect(roadmap.stages).toEqual([
      { id: 'structural', order: 0 },
      { id: 'connective', order: 1 },
      { id: 'classical', order: 2 },
    ])
    expect(roadmap.skills.length).toBeGreaterThan(0)
    expect(roadmap.puzzles.length).toBeGreaterThan(0)
    expect(unique(roadmap.skills.map(({ id }) => id))).toBe(true)
    expect(unique(roadmap.puzzles.map(({ id }) => id))).toBe(true)
    expect(new Set(roadmap.skills.map(({ stage }) => stage))).toEqual(new Set<Stage>([
      'structural', 'connective', 'classical',
    ]))
    expect(new Set(roadmap.puzzles.map(({ stage }) => stage))).toEqual(new Set<Stage>([
      'structural', 'connective', 'classical',
    ]))
  })

  it('gives every puzzle one primary evidence role and a stable folio position', () => {
    expect(roadmap.puzzles.map(({ folioOrder }) => folioOrder).sort((a, b) => a - b))
      .toEqual(Array.from({ length: roadmap.puzzles.length }, (_, index) => index))
    for (const puzzle of roadmap.puzzles) {
      expect(puzzle.evidence.filter(({ primary }) => primary)).toHaveLength(1)
      expect(puzzle.evidence[0]?.primary).toBe(true)
      expect(puzzle.sourceLabels.length).toBeGreaterThan(0)
    }
  })

  it('contains only resolved skill and puzzle references and has no cycles', () => {
    const skills = new Set(roadmap.skills.map(({ id }) => id))
    const puzzles = new Set(roadmap.puzzles.map(({ id }) => id))
    for (const skill of roadmap.skills) {
      expect(skill.prerequisites.every((id) => skills.has(id))).toBe(true)
    }
    expect(skills.has('distinguish-nested-owners')).toBe(true)
    expect(roadmap.skills.find(({ id }) => id === 'rewind-and-compare')?.mode).toBe('interface')
    expect(roadmap.skills.find(({ id }) => id === 'replace-retained-future')?.mode).toBe('interface')
    expect(puzzles.has('two-mark-projection')).toBe(true)
    for (const puzzle of roadmap.puzzles) {
      expect(puzzle.prerequisites.every((id) => puzzles.has(id))).toBe(true)
      expect(puzzle.evidence.every(({ skill }) => skills.has(skill))).toBe(true)
    }
    expect(findCycle(roadmap.skills.map(({ id, prerequisites }) => ({ id, prerequisites }))))
      .toBeNull()
    expect(findCycle(roadmap.puzzles.map(({ id, prerequisites }) => ({ id, prerequisites }))))
      .toBeNull()
  })

  it('supplies complete mastery evidence for every skill', () => {
    const evidence = evidenceBySkill(roadmap.puzzles)
    for (const skill of roadmap.skills) {
      const rows = evidence.get(skill.id) ?? []
      expect(idsFor(rows, 'introduction').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'contrast').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'application').length).toBeGreaterThanOrEqual(2)
      expect(idsFor(rows, 'retrieval').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'mixed').length).toBeGreaterThanOrEqual(1)
      expect(idsFor(rows, 'transfer').length).toBeGreaterThanOrEqual(1)
    }
  })

  it('derives required and optional content semantically from final transfer', () => {
    const required = prerequisiteClosure(roadmap.finalTransfer, roadmap.puzzles)
    const optional = roadmap.puzzles.filter(({ id }) => !required.has(id))
    for (const puzzle of optional) {
      expect(puzzle.evidence.every(({ role }) => role === 'remediation' || role === 'challenge'))
        .toBe(true)
    }
    expect(required.has(roadmap.finalTransfer)).toBe(true)
  })

  it('classifies every non-puzzle atlas label against a real puzzle', () => {
    const puzzles = new Set(roadmap.puzzles.map(({ id }) => id))
    for (const item of roadmap.internalLabels) {
      expect(item.label.trim()).not.toBe('')
      expect(item.reason.trim()).not.toBe('')
      expect(puzzles.has(item.puzzle)).toBe(true)
      expect(puzzles.has(item.label)).toBe(false)
    }
  })
})
