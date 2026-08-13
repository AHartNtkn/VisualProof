import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { singleStepAction } from '../../../src/kernel/proof/action'
import { ProofError } from '../../../src/kernel/proof/error'
import {
  loadTheory,
  theoryToJson,
  type Theory,
  verifyTheory,
} from '../../../src/kernel/proof/store'
import type { Theorem } from '../../../src/kernel/proof/theorem'

const PROPOSITION = relSig([])

function dropQ(): Theorem {
  const left = new DiagramBuilder()
  const p = left.atom(left.root, PROPOSITION)
  const q = left.atom(left.root, PROPOSITION)
  const boundary = left.wire( [
    { node: p, port: { kind: 'head' } },
    { node: q, port: { kind: 'head' } },
  ], PROPOSITION)
  const lhs = mkDiagramWithBoundary(left.build(), [boundary])

  const right = new DiagramBuilder()
  const rightP = right.atom(right.root, PROPOSITION)
  const rightBoundary = right.wire( [
    { node: rightP, port: { kind: 'head' } },
  ], PROPOSITION)
  const rhs = mkDiagramWithBoundary(right.build(), [rightBoundary])

  return {
    name: 'dropQ',
    lhs,
    rhs,
    actions: [singleStepAction('drop Q', {
      rule: 'erasure',
      sel: { region: lhs.diagram.root, regions: [], nodes: [q], wires: [] },
    })],
  }
}

function oneArgumentBody() {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, relSig([IOTA]))
  const argument = builder.wire( [{
    node: atom,
    port: { kind: 'arg', index: 0 },
  }])
  return mkDiagramWithBoundary(builder.build(), [argument])
}

function relationRefBody(defId: string) {
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, defId, relSig([IOTA]))
  const argument = builder.wire( [{
    node: ref,
    port: { kind: 'arg', index: 0 },
  }])
  return mkDiagramWithBoundary(builder.build(), [argument])
}

function refTheorem(defId: string, arity = 1): Theorem {
  const builder = new DiagramBuilder()
  const ref = builder.ref(
    builder.root,
    defId,
    relSig(Array.from({ length: arity }, () => IOTA)),
  )
  const boundary = builder.wire( [{
    node: ref,
    port: { kind: 'arg', index: 0 },
  }])
  const side = mkDiagramWithBoundary(builder.build(), [boundary])
  return { name: 'refThm', lhs: side, rhs: side, actions: [] }
}

function aliasedBody() {
  const builder = new DiagramBuilder()
  const shared = builder.wire( [], IOTA)
  return mkDiagramWithBoundary(builder.build(), [shared, shared])
}

function groupedNoop(): Theorem {
  const builder = new DiagramBuilder()
  const side = mkDiagramWithBoundary(builder.build(), [])
  return {
    name: 'groupedNoop',
    lhs: side,
    rhs: side,
    actions: [{
      label: 'introduce and eliminate a double cut',
      steps: [
        {
          rule: 'doubleCutIntro',
          sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] },
        },
        { rule: 'doubleCutElim', region: 'dc' },
      ],
      placements: [],
    }],
  }
}

describe('verifyTheory', () => {
  it('verifies relations and theorems in registration order', () => {
    const ctx = verifyTheory({
      relations: [['Unary', oneArgumentBody()]],
      theorems: [dropQ()],
    })

    expect(ctx.relations.has('Unary')).toBe(true)
    expect(ctx.theorems.has('dropQ')).toBe(true)
  })

  it('rejects duplicate theorem names and broken proofs by name', () => {
    const theorem = dropQ()
    expect(() => verifyTheory({ relations: [], theorems: [theorem, theorem] }))
      .toThrowError(/duplicate theorem name 'dropQ'/)

    const broken: Theorem = { ...theorem, actions: [] }
    expect(() => verifyTheory({ relations: [], theorems: [broken] }))
      .toThrow(ProofError)
  })

  it('allows citation of an earlier theorem but not a later one', () => {
    const base = dropQ()
    const derived: Theorem = {
      ...base,
      name: 'viaDropQ',
      actions: [singleStepAction('cite drop Q', {
        rule: 'theorem',
        name: 'dropQ',
        at: {
          sel: {
            region: base.lhs.diagram.root,
            regions: [],
            nodes: Object.keys(base.lhs.diagram.nodes),
            wires: [],
          },
          args: [...base.lhs.boundary],
        },
        direction: 'forward',
      })],
    }

    expect(() => verifyTheory({ relations: [], theorems: [base, derived] }))
      .not.toThrow()
    expect(() => verifyTheory({ relations: [], theorems: [derived, base] }))
      .toThrowError(/unknown theorem 'dropQ'/)
  })
})

describe('relation references', () => {
  it('verifies a theorem reference against an earlier definition', () => {
    const ctx = verifyTheory({
      relations: [['R', oneArgumentBody()]],
      theorems: [refTheorem('R')],
    })

    expect(ctx.relations.get('R')?.boundary).toHaveLength(1)
  })

  it('accepts a root-level unwitnessed relational wire in a body', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, relSig([IOTA]))
    const bound = builder.wire( [{
      node: atom,
      port: { kind: 'arg', index: 0 },
    }])
    const body = mkDiagramWithBoundary(builder.build(), [bound])
    const json = theoryToJson({ relations: [['R', body]], theorems: [] })

    expect(() => verifyTheory({ relations: [['R', body]], theorems: [] }))
      .not.toThrow()
    expect(loadTheory(JSON.parse(JSON.stringify(json))).ctx.relations.has('R'))
      .toBe(true)
  })

  it('preserves repeated boundary positions as one identity', () => {
    const body = aliasedBody()
    const json = theoryToJson({ relations: [['Alias', body]], theorems: [] })
    const { ctx } = loadTheory(JSON.parse(JSON.stringify(json)))

    expect(ctx.relations.get('Alias')?.boundary).toEqual(body.boundary)
  })

  it('rejects unknown references and arity mismatches', () => {
    expect(() => verifyTheory({ relations: [], theorems: [refTheorem('ghost')] }))
      .toThrowError(/names unknown relation 'ghost'/)
    expect(() => verifyTheory({
      relations: [['R', oneArgumentBody()]],
      theorems: [refTheorem('R', 2)],
    })).toThrowError(/signature '\(i,i\)' does not match.*signature '\(i\)'/)
  })

  it('permits only earlier relation references and preserves explicit order', () => {
    const ctx = verifyTheory({
      relations: [
        ['10', oneArgumentBody()],
        ['2', relationRefBody('10')],
        ['__proto__', relationRefBody('2')],
      ],
      theorems: [],
    })

    expect([...ctx.relations.keys()]).toEqual(['10', '2', '__proto__'])
    expect(() => verifyTheory({
      relations: [
        ['Alias', relationRefBody('Base')],
        ['Base', oneArgumentBody()],
      ],
      theorems: [],
    })).toThrowError(/names unknown relation 'Base'/)
  })

  it('rejects duplicate, self-recursive, and mutually recursive definitions', () => {
    expect(() => verifyTheory({
      relations: [['R', oneArgumentBody()], ['R', oneArgumentBody()]],
      theorems: [],
    })).toThrowError(/duplicate proof-context name 'R'/)
    expect(() => verifyTheory({
      relations: [['Loop', relationRefBody('Loop')]],
      theorems: [],
    })).toThrowError(/names unknown relation 'Loop'/)
    expect(() => verifyTheory({
      relations: [
        ['Left', relationRefBody('Right')],
        ['Right', relationRefBody('Left')],
      ],
      theorems: [],
    })).toThrowError(/names unknown relation 'Right'/)
  })
})

describe('check-before-register invariant', () => {
  it('refuses a theorem that cites itself', () => {
    const base = dropQ()
    const selfCite: Theorem = {
      ...base,
      name: 'selfCite',
      actions: [singleStepAction('self cite', {
        rule: 'theorem',
        name: 'selfCite',
        at: {
          sel: {
            region: base.lhs.diagram.root,
            regions: [],
            nodes: Object.keys(base.lhs.diagram.nodes),
            wires: [],
          },
          args: [...base.lhs.boundary],
        },
        direction: 'forward',
      })],
    }

    expect(() => verifyTheory({ relations: [], theorems: [selfCite] }))
      .toThrowError(/unknown theorem 'selfCite'/)
  })
})

describe('theory files', () => {
  it('writes and reloads only version 2', () => {
    const theory: Theory = {
      relations: [['Alias', aliasedBody()]],
      theorems: [dropQ(), groupedNoop()],
    }
    const encoded = theoryToJson(theory) as { version: number }

    expect(encoded.version).toBe(2)
    const text = JSON.stringify(encoded)
    const { theory: decoded, ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.has('dropQ')).toBe(true)
    expect(decoded.theorems[1]!.actions).toEqual(theory.theorems[1]!.actions)
    expect(JSON.stringify(theoryToJson(decoded))).toBe(text)
  })

  it('rejects version 1 rather than migrating it', () => {
    expect(() => loadTheory({
      format: 'visual-proof-theory',
      version: 1,
      relations: [],
      theorems: [],
    })).toThrowError(/unsupported version '1' \(expected 2\)/)
  })

  it('rejects unversioned, alien, and legacy relation envelopes', () => {
    expect(() => loadTheory({
      format: 'something-else',
      version: 2,
      relations: [],
      theorems: [],
    })).toThrowError(/format/)
    expect(() => loadTheory({
      format: 'visual-proof-theory',
      version: 99,
      relations: [],
      theorems: [],
    })).toThrowError(/version/)
    expect(() => loadTheory({
      format: 'visual-proof-theory',
      version: 2,
      relations: { R: {} },
      theorems: [],
    })).toThrowError(/'relations' and 'theorems' must be arrays/)
  })

  it('rejects duplicate relation pairs in version 2', () => {
    const encoded = theoryToJson({
      relations: [['R', oneArgumentBody()]],
      theorems: [],
    }) as {
      relations: unknown[]
    }

    expect(() => loadTheory({
      ...encoded,
      relations: [encoded.relations[0], encoded.relations[0]],
    })).toThrowError(/relations repeats name 'R'/)
  })
})
