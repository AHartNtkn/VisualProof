import { describe, expect, it } from 'vitest'
import * as validationModule from '../../scripts/validate-game-content'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import type { GameStep } from '../../src/game/types'

type StartViolationCode =
  | 'diagram-structure'
  | 'outer-goal'
  | 'prefix-arity'
  | 'branched-prefix'
  | 'interrupted-prefix'
  | 'matrix-bubble'
  | 'non-propositional-node'
  | 'individual-wire'
  | 'atom-region'
  | 'atom-binder'

type StartAnalysis = {
  readonly ok: boolean
  readonly goalCut: RegionId | null
  readonly prefix: readonly RegionId[]
  readonly matrixRoot: RegionId | null
  readonly violations: readonly { readonly code: StartViolationCode; readonly detail: string }[]
}

type WitnessAudit = {
  readonly ok: boolean
  readonly violations: readonly { readonly code: string; readonly detail: string }[]
}

type PropositionalShape = {
  readonly quantifierOrderFingerprint: string
  readonly immediateComplement: boolean
}

const authority = validationModule as typeof validationModule & {
  analyzeSeyricStart(diagram: Diagram): StartAnalysis
  auditSeyricWitness(diagram: Diagram, steps: readonly GameStep[]): WitnessAudit
  analyzeSeyricPropositionalShape(diagram: Diagram): PropositionalShape
}

const violationCodes = (analysis: StartAnalysis): readonly StartViolationCode[] =>
  analysis.violations.map(({ code }) => code)

const validGlobalPrefix = (): {
  readonly diagram: Diagram
  readonly goal: RegionId
  readonly outer: RegionId
  readonly inner: RegionId
} => {
  const builder = new DiagramBuilder()
  const goal = builder.cut(builder.root)
  const outer = builder.bubble(goal, 0)
  const inner = builder.bubble(outer, 0)
  const branch = builder.cut(inner)
  builder.atom(inner, outer)
  builder.atom(branch, inner)
  return { diagram: builder.build(), goal, outer, inner }
}

describe('Seyric authored-content authority', () => {
  it('accepts one global arity-zero binder prefix followed by a quantifier-free matrix', () => {
    const fixture = validGlobalPrefix()

    expect(authority.analyzeSeyricStart(fixture.diagram)).toEqual({
      ok: true,
      goalCut: fixture.goal,
      prefix: [fixture.outer, fixture.inner],
      matrixRoot: fixture.inner,
      violations: [],
    })
  })

  it('rejects a local bubble inside the propositional matrix', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const matrixBranch = builder.cut(goal)
    const local = builder.bubble(matrixBranch, 0)
    builder.atom(local, local)

    const result = authority.analyzeSeyricStart(builder.build())
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toContain('matrix-bubble')
  })

  it('rejects a branched bubble prefix', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const left = builder.bubble(goal, 0)
    const right = builder.bubble(goal, 0)
    builder.atom(left, left)
    builder.atom(right, right)

    const result = authority.analyzeSeyricStart(builder.build())
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toContain('branched-prefix')
  })

  it('rejects an interrupted prefix that places matrix content before another binder', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const outer = builder.bubble(goal, 0)
    builder.atom(outer, outer)
    const interrupted = builder.bubble(outer, 0)
    builder.atom(interrupted, interrupted)

    const result = authority.analyzeSeyricStart(builder.build())
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toContain('interrupted-prefix')
    expect(violationCodes(result)).toContain('matrix-bubble')
  })

  it('rejects nonzero prefix arity, non-atomic matrix nodes, and individual wires', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const binder = builder.bubble(goal, 1)
    builder.ref(binder, 'foreign-relation', 1)

    const result = authority.analyzeSeyricStart(builder.build())
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toEqual(expect.arrayContaining([
      'prefix-arity',
      'non-propositional-node',
      'individual-wire',
    ]))
  })

  it('returns structural violations for a missing or non-sheet root', () => {
    const missingRoot = {
      root: 'missing',
      regions: { r0: { kind: 'sheet' } },
      nodes: {},
      wires: {},
    } as Diagram
    const cutRoot = {
      root: 'r0',
      regions: { r0: { kind: 'cut', parent: 'r0' } },
      nodes: {},
      wires: {},
    } as Diagram

    for (const diagram of [missingRoot, cutRoot]) {
      expect(() => authority.analyzeSeyricStart(diagram)).not.toThrow()
      const result = authority.analyzeSeyricStart(diagram)
      expect(result.ok).toBe(false)
      expect(violationCodes(result)).toContain('diagram-structure')
    }
  })

  it('rejects missing parents and cyclic region ownership', () => {
    const missingParent = {
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'absent' },
      },
      nodes: {},
      wires: {},
    } as Diagram
    const cycle = {
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r2' },
        r2: { kind: 'cut', parent: 'r1' },
      },
      nodes: {},
      wires: {},
    } as Diagram

    for (const diagram of [missingParent, cycle]) {
      const result = authority.analyzeSeyricStart(diagram)
      expect(result.ok).toBe(false)
      expect(violationCodes(result)).toContain('diagram-structure')
    }
  })

  it('rejects an atom in a missing region and an atom with a nonexistent binder', () => {
    const fixture = validGlobalPrefix()
    const invalid = {
      ...fixture.diagram,
      nodes: {
        ...fixture.diagram.nodes,
        missingRegion: { kind: 'atom', region: 'absent-region', binder: fixture.outer },
        missingBinder: { kind: 'atom', region: fixture.inner, binder: 'absent-binder' },
      },
    } as Diagram

    const result = authority.analyzeSeyricStart(invalid)
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toEqual(expect.arrayContaining(['atom-region', 'atom-binder']))
  })

  it('rejects an atom bound by a local matrix bubble rather than the global prefix', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const prefix = builder.bubble(goal, 0)
    const branch = builder.cut(prefix)
    const local = builder.bubble(branch, 0)
    builder.atom(local, local)

    const result = authority.analyzeSeyricStart(builder.build())
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toEqual(expect.arrayContaining(['matrix-bubble', 'atom-binder']))
  })

  it('rejects an atom outside matrix ancestry even when it names a prefix binder', () => {
    const fixture = validGlobalPrefix()
    const invalid = {
      ...fixture.diagram,
      nodes: {
        ...fixture.diagram.nodes,
        outsideMatrix: { kind: 'atom', region: fixture.diagram.root, binder: fixture.outer },
      },
    } as Diagram

    const result = authority.analyzeSeyricStart(invalid)
    expect(result.ok).toBe(false)
    expect(violationCodes(result)).toEqual(expect.arrayContaining(['atom-region', 'atom-binder']))
  })

  it('accepts deepest-first terminal prefix cleanup followed by ordinary structural cleanup', () => {
    const fixture = validGlobalPrefix()
    const substantive = {
      rule: 'erasure',
      sel: { region: fixture.inner, regions: [], nodes: [], wires: [] },
    } as GameStep
    const witness: readonly GameStep[] = [
      substantive,
      { rule: 'vacuousElim', region: fixture.inner },
      { rule: 'vacuousElim', region: fixture.outer },
      { rule: 'doubleCutElim', region: fixture.goal },
      { rule: 'doubleCutElim', region: 'remaining-structural-pair' },
    ]

    expect(authority.auditSeyricWitness(fixture.diagram, witness)).toEqual({
      ok: true,
      violations: [],
    })
  })

  it('rejects early, reordered, or constructive quantifier operations in a Seyric witness', () => {
    const fixture = validGlobalPrefix()
    const lateSubstantive = {
      rule: 'erasure',
      sel: { region: fixture.inner, regions: [], nodes: [], wires: [] },
    } as GameStep
    const witnesses: readonly (readonly GameStep[])[] = [
      [
        { rule: 'vacuousElim', region: fixture.inner },
        lateSubstantive,
        { rule: 'vacuousElim', region: fixture.outer },
        { rule: 'doubleCutElim', region: fixture.goal },
      ],
      [
        { rule: 'vacuousElim', region: fixture.outer },
        { rule: 'vacuousElim', region: fixture.inner },
        { rule: 'doubleCutElim', region: fixture.goal },
      ],
      [
        { rule: 'vacuousIntro', sel: { region: fixture.inner, regions: [], nodes: [], wires: [] }, arity: 0 },
        { rule: 'vacuousElim', region: fixture.inner },
        { rule: 'vacuousElim', region: fixture.outer },
        { rule: 'doubleCutElim', region: fixture.goal },
      ],
    ]

    for (const witness of witnesses) {
      const result = authority.auditSeyricWitness(fixture.diagram, witness)
      expect(result.ok).toBe(false)
      expect(result.violations.length).toBeGreaterThan(0)
    }
  })

  it('rejects a double-cut elimination interleaved inside the prefix cleanup block', () => {
    const fixture = validGlobalPrefix()
    const witness: readonly GameStep[] = [
      { rule: 'vacuousElim', region: fixture.inner },
      { rule: 'doubleCutElim', region: 'interleaved-structural-pair' },
      { rule: 'vacuousElim', region: fixture.outer },
      { rule: 'doubleCutElim', region: fixture.goal },
    ]

    const result = authority.auditSeyricWitness(fixture.diagram, witness)
    expect(result.ok).toBe(false)
    expect(result.violations.map(({ code }) => code)).toContain('terminal-cleanup')
  })

  it('fingerprints matrix structure modulo global prefix order without collapsing cut topology', () => {
    const build = (swapBinders: boolean, extraCut: boolean): Diagram => {
      const builder = new DiagramBuilder()
      const goal = builder.cut(builder.root)
      const p = builder.bubble(goal, 0)
      const q = builder.bubble(p, 0)
      const branch = builder.cut(q)
      const nested = extraCut ? builder.cut(branch) : branch
      builder.atom(q, swapBinders ? q : p)
      builder.atom(nested, swapBinders ? p : q)
      return builder.build()
    }

    const original = authority.analyzeSeyricPropositionalShape(build(false, false))
    const reordered = authority.analyzeSeyricPropositionalShape(build(true, false))
    const differentTopology = authority.analyzeSeyricPropositionalShape(build(true, true))

    expect(reordered.quantifierOrderFingerprint).toBe(original.quantifierOrderFingerprint)
    expect(differentTopology.quantifierOrderFingerprint).not.toBe(
      original.quantifierOrderFingerprint,
    )
  })

  it('preserves prefix cardinality when the extra proposition binder is vacuous', () => {
    const bare = new DiagramBuilder()
    const bareGoal = bare.cut(bare.root)
    bare.cut(bareGoal)

    const ringed = new DiagramBuilder()
    const ringedGoal = ringed.cut(ringed.root)
    const vacuous = ringed.bubble(ringedGoal, 0)
    ringed.cut(vacuous)

    expect(authority.analyzeSeyricPropositionalShape(ringed.build()).quantifierOrderFingerprint)
      .not.toBe(authority.analyzeSeyricPropositionalShape(bare.build()).quantifierOrderFingerprint)
  })

  it('detects direct atomic and sibling-group complements without treating an implication chain as immediate', () => {
    const atomic = new DiagramBuilder()
    const atomicGoal = atomic.cut(atomic.root)
    const p = atomic.bubble(atomicGoal, 0)
    atomic.atom(p, p)
    const notP = atomic.cut(p)
    atomic.atom(notP, p)

    const compound = new DiagramBuilder()
    const compoundGoal = compound.cut(compound.root)
    const cp = compound.bubble(compoundGoal, 0)
    const cq = compound.bubble(cp, 0)
    compound.atom(cq, cp)
    compound.atom(cq, cq)
    const notCompound = compound.cut(cq)
    compound.atom(notCompound, cp)
    compound.atom(notCompound, cq)

    const chain = new DiagramBuilder()
    const chainGoal = chain.cut(chain.root)
    const xp = chain.bubble(chainGoal, 0)
    const xq = chain.bubble(xp, 0)
    const xr = chain.bubble(xq, 0)
    const firstLink = chain.cut(xr)
    chain.atom(firstLink, xp)
    const firstResult = chain.cut(firstLink)
    chain.atom(firstResult, xq)
    const secondLink = chain.cut(xr)
    chain.atom(secondLink, xq)
    const secondResult = chain.cut(secondLink)
    chain.atom(secondResult, xr)
    chain.atom(xr, xp)

    expect(authority.analyzeSeyricPropositionalShape(atomic.build()).immediateComplement)
      .toBe(true)
    expect(authority.analyzeSeyricPropositionalShape(compound.build()).immediateComplement)
      .toBe(true)
    expect(authority.analyzeSeyricPropositionalShape(chain.build()).immediateComplement)
      .toBe(false)
  })

  it('rejects a near compound whose sibling group has a different proposition owner', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const p = builder.bubble(goal, 0)
    const q = builder.bubble(p, 0)
    const r = builder.bubble(q, 0)
    builder.atom(r, p)
    builder.atom(r, q)
    const deniedNearShape = builder.cut(r)
    builder.atom(deniedNearShape, p)
    builder.atom(deniedNearShape, r)

    expect(authority.analyzeSeyricPropositionalShape(builder.build()).immediateComplement)
      .toBe(false)
  })

  it('rejects an atomic silhouette whose binder attachment differs', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const p = builder.bubble(goal, 0)
    const q = builder.bubble(p, 0)
    builder.atom(q, p)
    const deniedOtherOwner = builder.cut(q)
    builder.atom(deniedOtherOwner, q)

    expect(authority.analyzeSeyricPropositionalShape(builder.build()).immediateComplement)
      .toBe(false)
  })

  it('does not mistake a genuine De Morgan transformation for an exact occurrence', () => {
    const builder = new DiagramBuilder()
    const goal = builder.cut(builder.root)
    const p = builder.bubble(goal, 0)
    const q = builder.bubble(p, 0)
    const r = builder.bubble(q, 0)

    builder.atom(r, p)
    const transformedSource = builder.cut(r)
    const sourceSum = builder.cut(transformedSource)
    const sourceNotQ = builder.cut(sourceSum)
    const sourceNotR = builder.cut(sourceSum)
    builder.atom(sourceNotQ, q)
    builder.atom(sourceNotR, r)

    const deniedProduct = builder.cut(r)
    builder.atom(deniedProduct, p)
    const targetNotQ = builder.cut(deniedProduct)
    const targetNotR = builder.cut(deniedProduct)
    builder.atom(targetNotQ, q)
    builder.atom(targetNotR, r)

    expect(authority.analyzeSeyricPropositionalShape(builder.build()).immediateComplement)
      .toBe(false)
  })
})
