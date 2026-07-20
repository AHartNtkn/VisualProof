import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { isBlank } from '../../src/game/blank'
import {
  analyzeSeyricPropositionalShape,
  analyzeSeyricStart,
  auditSeyricWitness,
} from '../../src/game/content/seyric-authority'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { stepFromJson } from '../../src/kernel/proof/json'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

const redesignedIds = [
  'alternating-negation-cnf',
  'alternating-negation-dnf',
  'de-morgan-sum-consumer',
  'classical-consensus-branch-building',
  'preserve-sole-structural-source',
] as const

type RedesignedId = typeof redesignedIds[number]
type PuzzleFile = { readonly id: string; readonly diagram: unknown }
type ValidationFile = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
  readonly expectedRules: readonly string[]
  readonly recognizedStates: readonly unknown[]
}

const context = { theorems: new Map(), relations: new Map() }
const content = <T>(relativePath: string): T =>
  JSON.parse(readFileSync(resolve(process.cwd(), 'content', relativePath), 'utf8')) as T
const puzzle = (id: string): Diagram =>
  diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)
const witness = (id: string): readonly ProofStep[] =>
  content<ValidationFile>(`validation/${id}.json`).solution.map(stepFromJson)
const replay = (diagram: Diagram, steps: readonly ProofStep[]): Diagram =>
  steps.reduce((state, step) => applyStep(state, step, context, 'backward'), diagram)
const replayAttempt = (diagram: Diagram, steps: readonly ProofStep[]): Diagram | null => {
  try {
    return replay(diagram, steps)
  } catch {
    return null
  }
}

const criticalStepIndexes = (
  id: RedesignedId,
  steps: readonly ProofStep[],
): readonly number[] => {
  const beforeCleanup = steps.findIndex((step) => step.rule === 'vacuousElim')
  const candidates = steps.slice(0, beforeCleanup < 0 ? steps.length : beforeCleanup)

  switch (id) {
    case 'alternating-negation-cnf':
      return candidates.flatMap((step, index) =>
        step.rule === 'deiteration' || step.rule === 'doubleCutIntro' || step.rule === 'iteration'
          ? [index]
          : [])
    case 'alternating-negation-dnf':
      return candidates.flatMap((step, index) =>
        step.rule === 'deiteration' || step.rule === 'doubleCutIntro' ? [index] : [])
    case 'de-morgan-sum-consumer':
      return candidates.flatMap((step, index) => step.rule === 'deiteration' ? [index] : [])
    case 'classical-consensus-branch-building':
      return candidates.flatMap((step, index) =>
        step.rule === 'doubleCutIntro' || step.rule === 'iteration' || step.rule === 'deiteration'
          ? [index]
          : [])
    case 'preserve-sole-structural-source':
      return candidates.flatMap((step, index) =>
        step.rule === 'iteration' || step.rule === 'deiteration' ? [index] : [])
  }
}

describe('mixed Seyric collision redesigns', () => {
  it('provides five clean, shortcut-free, replayable Seyric problems', () => {
    for (const id of redesignedIds) {
      const diagram = puzzle(id)
      const steps = witness(id)
      const validation = content<ValidationFile>(`validation/${id}.json`)

      expect(analyzeSeyricStart(diagram).violations, id).toEqual([])
      expect(auditSeyricWitness(diagram, steps).violations, id).toEqual([])
      expect(analyzeSeyricPropositionalShape(diagram).immediateComplement, id).toBe(false)
      expect(validation.availableArtifacts, id).toEqual([])
      expect(validation.recognizedStates, id).toEqual([])
      expect(validation.expectedRules, id).toEqual([...new Set(steps.map((step) => step.rule))])
      expect(isBlank(replay(diagram, steps)), `${id} witness must reach blank`).toBe(true)
    }
  })

  it('is structurally distinct from every other Seyric problem modulo global-prefix order', () => {
    const coverage = content<{
      readonly puzzles: readonly { readonly puzzle: string }[]
    }>('coverage/seyric.json')
    const owners = new Map<string, string>()

    for (const { puzzle: id } of coverage.puzzles) {
      const fingerprint = analyzeSeyricPropositionalShape(puzzle(id)).quantifierOrderFingerprint
      const prior = owners.get(fingerprint)
      if (
        redesignedIds.includes(id as RedesignedId)
        || (prior !== undefined && redesignedIds.includes(prior as RedesignedId))
      ) {
        expect(prior, `${id} duplicates ${prior ?? 'no prior problem'}`).toBeUndefined()
      }
      owners.set(fingerprint, id)
    }
  })

  it('makes each role-bearing construction causally necessary in its authored witness', () => {
    for (const id of redesignedIds) {
      const diagram = puzzle(id)
      const steps = witness(id)
      const critical = criticalStepIndexes(id, steps)
      expect(critical.length, `${id} must contain role-bearing proof work`).toBeGreaterThan(0)

      for (const omitted of critical) {
        const counterfactual = replayAttempt(diagram, steps.filter((_, index) => index !== omitted))
        expect(counterfactual === null || !isBlank(counterfactual), `${id} omission ${omitted}`).toBe(true)
      }
    }
  })

  it('makes the sole structural source serve more than one downstream occurrence', () => {
    const diagram = puzzle('preserve-sole-structural-source')
    const steps = witness('preserve-sole-structural-source')
    const [leftUse, , rightUse] = steps
    expect(leftUse).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r5', regions: [], nodes: ['n1'] },
    })
    expect(rightUse).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r7', regions: [], nodes: ['n3'] },
    })

    if (leftUse?.rule !== 'deiteration' || rightUse?.rule !== 'deiteration') {
      throw new Error('expected the two branch uses to be deiterations')
    }
    const leftNode = diagram.nodes[leftUse.sel.nodes[0]!]
    const rightNode = diagram.nodes[rightUse.sel.nodes[0]!]
    expect(leftNode?.kind).toBe('atom')
    expect(rightNode?.kind).toBe('atom')
    if (leftNode?.kind !== 'atom' || rightNode?.kind !== 'atom') {
      throw new Error('expected both branch uses to select proposition atoms')
    }
    expect(leftNode.binder).toBe('r2')
    expect(rightNode.binder).toBe('r2')

    expect(() => applyStep(diagram, leftUse, context, 'backward')).not.toThrow()
    expect(() => applyStep(diagram, rightUse, context, 'backward')).not.toThrow()

    const sourceRemoved = applyStep(diagram, stepFromJson({
      rule: 'erasure',
      sel: { region: 'r4', regions: [], nodes: ['n0'], wires: [] },
    }), context, 'backward')
    expect(() => applyStep(sourceRemoved, leftUse, context, 'backward')).toThrow()
    expect(() => applyStep(sourceRemoved, rightUse, context, 'backward')).toThrow()
  })

  it('makes the consensus factor non-erasable initially and consumes it in both branches', () => {
    const diagram = puzzle('classical-consensus-branch-building')
    const steps = witness('classical-consensus-branch-building')
    const factorNodes = ['n6', 'n7'] as const

    for (const node of factorNodes) {
      const region = diagram.nodes[node]?.region
      expect(region, `${node} must be present`).toBeDefined()
      expect(() => applyStep(diagram, stepFromJson({
        rule: 'erasure',
        sel: { region, regions: [], nodes: [node], wires: [] },
      }), context, 'backward'), `${node} must not be initially erasable`).toThrow()
    }

    const factorUses = steps.flatMap((step, index) => step.rule === 'deiteration'
      && step.sel.nodes.length === 1
      && factorNodes.includes(step.sel.nodes[0] as typeof factorNodes[number])
      ? [index]
      : [])
    expect(factorUses).toHaveLength(2)
    for (const omitted of factorUses) {
      const attempt = replayAttempt(diagram, steps.filter((_, index) => index !== omitted))
      expect(attempt === null || !isBlank(attempt)).toBe(true)
    }
  })

  it('rejects the former erase-both-factors consensus bypass', () => {
    const diagram = puzzle('classical-consensus-branch-building')
    const bypass = [
      stepFromJson({
        rule: 'erasure',
        sel: { region: 'r6', regions: [], nodes: ['n6'], wires: [] },
      }),
      stepFromJson({
        rule: 'erasure',
        sel: { region: 'r9', regions: [], nodes: ['n7'], wires: [] },
      }),
      stepFromJson({ rule: 'doubleCutElim', region: 'r12' }),
      stepFromJson({
        rule: 'deiteration',
        sel: { region: 'r5', regions: ['r7'], nodes: [], wires: [] },
        fuel: 100,
      }),
      stepFromJson({ rule: 'doubleCutElim', region: 'r5' }),
      stepFromJson({
        rule: 'deiteration',
        sel: { region: 'r8', regions: ['r11'], nodes: [], wires: [] },
        fuel: 100,
      }),
      stepFromJson({ rule: 'doubleCutElim', region: 'r8' }),
      stepFromJson({
        rule: 'deiteration',
        sel: { region: 'r10', regions: [], nodes: ['n2'], wires: [] },
        fuel: 100,
      }),
      stepFromJson({
        rule: 'erasure',
        sel: { region: 'r16', regions: ['r14', 'r15'], nodes: ['n0'], wires: [] },
      }),
      stepFromJson({ rule: 'vacuousElim', region: 'r16' }),
      stepFromJson({ rule: 'vacuousElim', region: 'r4' }),
      stepFromJson({ rule: 'vacuousElim', region: 'r3' }),
      stepFromJson({ rule: 'vacuousElim', region: 'r2' }),
      stepFromJson({ rule: 'doubleCutElim', region: 'r1' }),
    ]

    const attempt = replayAttempt(diagram, bypass)
    expect(attempt === null || !isBlank(attempt)).toBe(true)
  })
})
