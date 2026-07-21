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
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { actionFromJson } from '../../src/kernel/proof/json'
import { findDeiterationEvidence } from '../../src/kernel/rules/iteration'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'

const redesignedIds = [
  'marked-echo-deiteration',
  'atomic-content-insertion',
  'structural-recognition-routing-choice',
  'weakening-injection-weave',
  'sey-red-c01',
  'grouped-branch-construction',
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

const replay = (start: Diagram, steps: readonly ProofStep[]): Diagram =>
  steps.reduce(
    (diagram, step) => applyStep(diagram, step, context, 'backward'),
    start,
  )

const directItems = (diagram: Diagram, region: RegionId) => [
  ...Object.entries(diagram.regions)
    .filter(([, candidate]) => candidate.kind !== 'sheet' && candidate.parent === region)
    .map(([id]) => ({ kind: 'region' as const, id })),
  ...Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => ({ kind: 'node' as const, id })),
]

const complementShortcutDepth = (diagram: Diagram): 0 | 1 | null => {
  if (analyzeSeyricPropositionalShape(diagram).immediateComplement) return 0
  for (const [region, value] of Object.entries(diagram.regions)) {
    if (value.kind !== 'cut') continue
    try {
      const opened = applyStep(diagram, { rule: 'doubleCutElim', region }, context, 'backward')
      if (analyzeSeyricStart(opened).ok
        && analyzeSeyricPropositionalShape(opened).immediateComplement) return 1
    } catch {
      // Not an eliminable annulus.
    }
  }
  return null
}

const closureSize = (diagram: Diagram, root: RegionId): { regions: number; nodes: number } => {
  const regions = new Set([root])
  let changed = true
  while (changed) {
    changed = false
    for (const [id, region] of Object.entries(diagram.regions)) {
      if (region.kind === 'sheet' || regions.has(id) || !regions.has(region.parent)) continue
      regions.add(id)
      changed = true
    }
  }
  return {
    regions: regions.size,
    nodes: Object.values(diagram.nodes).filter((node) => regions.has(node.region)).length,
  }
}

describe('redesigned Seyric shortcut puzzles', () => {
  it('removes the accidental exposed-complement routes and classifies the one retained exception', () => {
    for (const id of redesignedIds.filter((candidate) => candidate !== 'sey-red-c01')) {
      expect(complementShortcutDepth(puzzle(id)), id).toBeNull()
    }
    expect(complementShortcutDepth(puzzle('sey-red-c01'))).toBe(0)
  })

  it('keeps the intimidating exception as one simple core beside one coherent large junk fragment', () => {
    const diagram = puzzle('sey-red-c01')
    const matrix = analyzeSeyricStart(diagram).matrixRoot!
    const items = directItems(diagram, matrix)
    expect(items).toHaveLength(3)

    const junk = items.find(({ kind, id }) =>
      kind === 'region'
      && diagram.regions[id]?.kind === 'cut'
      && closureSize(diagram, id).regions >= 6)
    expect(junk).toBeDefined()
    expect(closureSize(diagram, junk!.id)).toEqual({ regions: 6, nodes: 6 })
  })

  it('keeps grouped construction outside the two-variable compound excluded-middle family', () => {
    const grouped = boundaryForm({ diagram: puzzle('grouped-branch-construction'), boundary: [] })
    const compoundLem = boundaryForm({ diagram: puzzle('sey-lem-i01'), boundary: [] })
    expect(grouped).not.toBe(compoundLem)
  })

  it('uses an exact marked ancestor fragment rather than an atom inside that fragment', () => {
    const diagram = puzzle('marked-echo-deiteration')
    const exact = applyStep(diagram, witness('marked-echo-deiteration')[0]!, context, 'backward')
    expect(exact).not.toEqual(diagram)
    const atomOnly = { region: 'r6', regions: [], nodes: ['n1'], wires: [] }
    expect(() => findDeiterationEvidence(diagram, atomOnly, 100)).toThrow()
  })

  it('makes a bound relation spawn create the exact source consumed by the next step', () => {
    const diagram = puzzle('atomic-content-insertion')
    const [spawn, consume] = witness('atomic-content-insertion')
    expect(spawn).toEqual({ rule: 'boundRelationSpawn', region: 'r5', binder: 'r3', arity: 0 })
    const exact = applyStep(diagram, spawn!, context, 'backward')
    expect(() => applyStep(exact, consume!, context, 'backward')).not.toThrow()
    expect(() => applyStep(diagram, consume!, context, 'backward')).toThrow()

    const withWrongShape = applyStep(diagram, {
      rule: 'boundRelationSpawn', region: 'r5', binder: 'r2', arity: 0,
    }, context, 'backward')
    expect(() => applyStep(withWrongShape, consume!, context, 'backward')).toThrow()
  })

  it('routes an intact marked source before the downstream atomic route exists', () => {
    const diagram = puzzle('structural-recognition-routing-choice')
    const steps = witness('structural-recognition-routing-choice')
    expect(() => applyStep(diagram, steps[0]!, context, 'backward')).not.toThrow()
    expect(() => findDeiterationEvidence(diagram, {
      region: 'r8', regions: [], nodes: ['n2'], wires: [],
    }, 100)).toThrow()
    expect(() => applyStep(diagram, steps[3]!, context, 'backward')).toThrow()
    const routed = replay(diagram, steps.slice(0, 4))
    expect(() => applyStep(routed, steps[4]!, context, 'backward')).not.toThrow()
  })

  it('makes weakening create the whole source placed by injection and consumed downstream', () => {
    const diagram = puzzle('weakening-injection-weave')
    const steps = witness('weakening-injection-weave')
    const [weakenSource, placeSource, removeSpare, exposeChoice, exposeT, consumeT] = steps

    expect(weakenSource).toMatchObject({
      rule: 'erasure',
      sel: { region: 'r9', regions: [], nodes: ['n2'] },
    })
    expect(placeSource).toMatchObject({
      rule: 'deiteration',
      sel: { region: 'r12', regions: ['r13'], nodes: [] },
    })
    expect(removeSpare).toMatchObject({
      rule: 'erasure',
      sel: { region: 'r11', regions: ['r15'], nodes: [] },
    })

    expect(complementShortcutDepth(diagram)).toBeNull()
    expect(() => applyStep(diagram, placeSource!, context, 'backward')).toThrow()
    const weakened = applyStep(diagram, weakenSource!, context, 'backward')
    const sourcePlaced = applyStep(weakened, placeSource!, context, 'backward')
    const branchSelected = applyStep(sourcePlaced, removeSpare!, context, 'backward')
    const choiceExposed = applyStep(branchSelected, exposeChoice!, context, 'backward')
    const tExposed = applyStep(choiceExposed, exposeT!, context, 'backward')
    expect(() => applyStep(diagram, consumeT!, context, 'backward')).toThrow()
    expect(() => applyStep(tExposed, consumeT!, context, 'backward')).not.toThrow()

    const oldBoundaryOpened = applyStep(
      diagram,
      { rule: 'doubleCutElim', region: 'r8' },
      context,
      'backward',
    )
    expect(() => findDeiterationEvidence(oldBoundaryOpened, {
      region: 'r6', regions: ['r7'], nodes: ['n2'], wires: [],
    }, 100)).toThrow()
  })

  it('requires removal of the intact grouped junk branch in the current witness', () => {
    const diagram = puzzle('grouped-branch-construction')
    const steps = witness('grouped-branch-construction')
    const [removeJunk] = steps
    expect(removeJunk).toEqual({
      rule: 'erasure',
      sel: { region: 'r8', regions: ['r9'], nodes: [], wires: [] },
    })
    expect(diagram.regions.r9).toEqual({ kind: 'cut', parent: 'r8' })
    expect(['n4', 'n5'].map((id) => diagram.nodes[id])).toEqual([
      { kind: 'atom', region: 'r9', binder: 'r2' },
      { kind: 'atom', region: 'r9', binder: 'r3' },
    ])
    expect(isBlank(replay(diagram, steps))).toBe(true)
    expect(() => replay(diagram, steps.slice(1))).toThrow()
  })

  it('keeps every redesigned puzzle structurally Seyric, replayable, witness-clean, and canonically unique', () => {
    const allPaths = readdirSync(resolve(process.cwd(), 'content/puzzles'))
      .filter((name) => name.endsWith('.json'))
    const otherForms = new Map<string, string>()
    for (const name of allPaths) {
      const id = name.slice(0, -5)
      if (redesignedIds.includes(id as typeof redesignedIds[number])) continue
      otherForms.set(boundaryForm({ diagram: puzzle(id), boundary: [] }), id)
    }

    const redesignedForms = new Set<string>()
    for (const id of redesignedIds) {
      const diagram = puzzle(id)
      const steps = witness(id)
      expect(analyzeSeyricStart(diagram).violations, id).toEqual([])
      expect(auditSeyricWitness(diagram, steps).violations, id).toEqual([])
      expect(isBlank(replay(diagram, steps)), id).toBe(true)
      const form = boundaryForm({ diagram, boundary: [] })
      expect(otherForms.get(form), `${id} duplicates current start`).toBeUndefined()
      expect(redesignedForms.has(form), `${id} duplicates another redesign`).toBe(false)
      redesignedForms.add(form)
    }
  })
})
