import { readFileSync, readdirSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { isBlank } from '../../src/game/blank'
import {
  analyzeSeyricPropositionalShape,
  analyzeSeyricStart,
  auditSeyricWitness,
} from '../../src/game/content/seyric-authority'
import { boundaryForm } from '../../src/kernel/diagram/canonical/explore'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { actionFromJson } from '../../src/kernel/proof/json'
import { findDeiterationEvidence } from '../../src/kernel/rules/iteration'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

const repairedIds = [
  'marked-echo-deiteration',
  'rm-fa',
  'conjunction-reassociation-role-scope',
] as const

type PuzzleFile = { readonly id: string; readonly diagram: unknown }
type ValidationFile = {
  readonly puzzle: string
  readonly solution: readonly unknown[]
  readonly availableArtifacts: readonly string[]
  readonly expectedRules: readonly string[]
  readonly recognizedStates: readonly unknown[]
}

const context = EMPTY_PROOF_CONTEXT
const content = <T>(relativePath: string): T =>
  JSON.parse(readFileSync(resolve(process.cwd(), 'content', relativePath), 'utf8')) as T
const puzzle = (id: string): Diagram =>
  diagramFromJson(content<PuzzleFile>(`puzzles/${id}.json`).diagram)
const witness = (id: string): readonly ProofStep[] =>
  content<ValidationFile>(`validation/${id}.json`).solution
    .map((action, index) => actionFromJson(action, `${id} solution action ${index}`))
    .flatMap((action) => action.steps)
const deiteration = (diagram: Diagram, sel: Extract<ProofStep, { rule: 'deiteration' }>['sel']): ProofStep => ({
  rule: 'deiteration', sel, ...findDeiterationEvidence(diagram, sel, 100),
})
const replay = (diagram: Diagram, steps: readonly ProofStep[]): Diagram =>
  steps.reduce((state, step) => applyStep(state, step, context, 'backward'), diagram)
const attempt = (diagram: Diagram, steps: readonly ProofStep[]): Diagram | null => {
  try {
    return replay(diagram, steps)
  } catch {
    return null
  }
}

describe('Seyric causal shortcut repairs', () => {
  it('keeps each stable record Seyric, exact-shortcut-free, replayable, and clean', () => {
    for (const id of repairedIds) {
      const puzzleFile = content<PuzzleFile>(`puzzles/${id}.json`)
      const validation = content<ValidationFile>(`validation/${id}.json`)
      const diagram = diagramFromJson(puzzleFile.diagram)
      const steps = validation.solution
        .map((action, index) => actionFromJson(action, `${id} solution action ${index}`))
        .flatMap((action) => action.steps)

      expect(puzzleFile.id, id).toBe(id)
      expect(validation.puzzle, id).toBe(id)
      expect(validation.availableArtifacts, id).toEqual([])
      expect(validation.recognizedStates, id).toEqual([])
      expect(validation.expectedRules, id).toEqual([...new Set(steps.map((step) => step.rule))])
      expect(analyzeSeyricStart(diagram).violations, id).toEqual([])
      expect(analyzeSeyricPropositionalShape(diagram).immediateComplement, id).toBe(false)
      expect(auditSeyricWitness(diagram, steps).violations, id).toEqual([])
      expect(isBlank(replay(diagram, steps)), id).toBe(true)
    }
  })

  it('makes the exact marked fragment unlock a differently shaped continuation', () => {
    const diagram = puzzle('marked-echo-deiteration')
    const steps = witness('marked-echo-deiteration')
    const [removeEcho, exposeQ, consumeQ] = steps

    expect(removeEcho).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r6', regions: ['r7'], nodes: [] },
    })
    expect(exposeQ).toEqual({ rule: 'doubleCutElim', region: 'r6' })
    expect(consumeQ).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r9', regions: [], nodes: ['n3'] },
    })

    expect(() => applyStep(diagram, exposeQ!, context, 'backward')).toThrow()
    expect(() => applyStep(diagram, consumeQ!, context, 'backward')).toThrow()
    expect(() => deiteration(diagram, {
      region: 'r6', regions: ['r7', 'r8'], nodes: [], wires: [],
    })).toThrow()

    const echoRemoved = applyStep(diagram, removeEcho!, context, 'backward')
    const qExposed = applyStep(echoRemoved, exposeQ!, context, 'backward')
    expect(() => applyStep(qExposed, consumeQ!, context, 'backward')).not.toThrow()
  })

  it('makes compound factoring produce the exact resource consumed downstream', () => {
    const diagram = puzzle('rm-fa')
    const steps = witness('rm-fa')
    const [matchSource, exposeFactor, consumeFactor, exposeU] = steps

    expect(matchSource).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r16', regions: ['r17'], nodes: [] },
    })
    expect(exposeFactor).toEqual({ rule: 'doubleCutElim', region: 'r16' })
    expect(consumeFactor).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r33', regions: ['r34', 'r37'], nodes: [] },
    })
    expect(exposeU).toEqual({ rule: 'doubleCutElim', region: 'r33' })

    expect(() => applyStep(diagram, consumeFactor!, context, 'backward')).toThrow()
    expect(() => deiteration(diagram, {
      region: 'r16', regions: ['r17', 'r26'], nodes: [], wires: [],
    })).toThrow()

    const factorReady = replay(diagram, [matchSource!, exposeFactor!])
    expect(factorReady.regions.r27).toMatchObject({ parent: 'r40' })
    expect(factorReady.regions.r30).toMatchObject({ parent: 'r40' })
    const factorConsumed = applyStep(factorReady, consumeFactor!, context, 'backward')
    expect(() => applyStep(factorConsumed, exposeU!, context, 'backward')).not.toThrow()
  })

  it('requires the full flat three-role product rather than its compound subrole', () => {
    const diagram = puzzle('conjunction-reassociation-role-scope')
    const steps = witness('conjunction-reassociation-role-scope')
    const [consumeProduct, exposeT] = steps

    expect(consumeProduct).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r11', regions: ['r12'], nodes: ['n4', 'n5'] },
    })
    expect(exposeT).toEqual({ rule: 'doubleCutElim', region: 'r11' })

    const compoundOnly = applyStep(diagram, deiteration(diagram, {
      region: 'r11', regions: ['r12'], nodes: [], wires: [],
    }), context, 'backward')
    expect(() => applyStep(compoundOnly, exposeT!, context, 'backward')).toThrow()

    const atomsOnly = applyStep(diagram, deiteration(diagram, {
      region: 'r11', regions: [], nodes: ['n4', 'n5'], wires: [],
    }), context, 'backward')
    expect(() => applyStep(atomsOnly, exposeT!, context, 'backward')).toThrow()

    const fullProduct = applyStep(diagram, consumeProduct!, context, 'backward')
    expect(() => applyStep(fullProduct, exposeT!, context, 'backward')).not.toThrow()

    const compoundBypass = attempt(diagram, [
      deiteration(diagram, {
        region: 'r11', regions: ['r12'], nodes: [], wires: [],
      }),
      ...steps.slice(1),
    ])
    expect(compoundBypass === null || !isBlank(compoundBypass)).toBe(true)
  })

  it('keeps all three starts canonically distinct from the rest of the collection', () => {
    const owners = new Map<string, string>()
    for (const filename of readdirSync(resolve(process.cwd(), 'content/puzzles'))) {
      if (!filename.endsWith('.json')) continue
      const id = filename.slice(0, -5)
      const form = boundaryForm({ diagram: puzzle(id), boundary: [] })
      const prior = owners.get(form)
      if (
        repairedIds.includes(id as typeof repairedIds[number])
        || (prior !== undefined && repairedIds.includes(prior as typeof repairedIds[number]))
      ) expect(prior, `${id} duplicates ${prior ?? 'no prior puzzle'}`).toBeUndefined()
      owners.set(form, id)
    }
  })
})
