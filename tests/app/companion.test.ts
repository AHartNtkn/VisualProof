import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkReplay } from '../../src/app/replay'
import { companionFor } from '../../src/app/companion'

describe('replay companion', () => {
  it('is absent from edit and proving modes', () => {
    expect(companionFor({ mode: 'edit', replay: null })).toBeNull()
    expect(companionFor({ mode: 'prove', replay: null })).toBeNull()
  })

  it('is absent from replay until a verified replay exists', () => {
    expect(companionFor({ mode: 'replay', replay: null })).toBeNull()
  })

  it('shows the immutable final replay state', () => {
    const builder = new DiagramBuilder()
    builder.termNode(builder.root, parseTerm('\\x. x'))
    const statement = mkDiagramWithBoundary(builder.build(), [])
    const replay = mkReplay({ name: 'identity', lhs: statement, rhs: statement, actions: [] }, verifyTheory(buildFregeTheory()))
    const companion = companionFor({ mode: 'replay', replay })
    expect(companion).toEqual({ diagram: statement.diagram, boundary: [], label: 'goal: final state' })
  })
})
