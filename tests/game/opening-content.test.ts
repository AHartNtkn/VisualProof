import { describe, expect, it } from 'vitest'
import { isBlank } from '../../src/game/blank'
import { isRequired } from '../../src/game/progress'
import { applyGameStep, currentDiagram, startPuzzle } from '../../src/game/session'
import { cultureId, performanceId, puzzleId } from '../../src/game/types'
import { openingCatalog, openingCatalogSource } from '../../src/game/content'

const puzzleIds = [
  'two-veils',
  'four-veils',
  'forked-veil',
  'echoed-veil',
  'single-mark-return',
  'two-mark-projection',
  'blank-witness',
] as const

const authorityFor = (catalog: ReturnType<typeof openingCatalog>) => ({
  context: catalog.source.context,
  puzzle: catalog.puzzle,
  canUseVellum: () => false,
})

const rules = (id: typeof puzzleIds[number]) =>
  openingCatalog().puzzle(puzzleId(id)).witness.map((step) => step.rule)

const structure = (id: typeof puzzleIds[number]) => {
  const diagram = openingCatalog().puzzle(puzzleId(id)).goal.diagram
  const regions = Object.values(diagram.regions)
  const nodes = Object.values(diagram.nodes)
  const bubbles = Object.entries(diagram.regions)
    .filter((entry): entry is [string, Extract<(typeof regions)[number], { kind: 'bubble' }>] =>
      entry[1].kind === 'bubble')
  return {
    sheets: regions.filter((region) => region.kind === 'sheet').length,
    cuts: regions.filter((region) => region.kind === 'cut').length,
    bubbleArities: bubbles.map(([, bubble]) => bubble.arity).sort(),
    atomsPerBinder: bubbles.map(([binder]) =>
      nodes.filter((node) => node.kind === 'atom' && node.binder === binder).length).sort(),
    atoms: nodes.filter((node) => node.kind === 'atom').length,
    terms: nodes.filter((node) => node.kind === 'term').length,
    refs: nodes.filter((node) => node.kind === 'ref').length,
  }
}

describe('permanent opening catalog', () => {
  it('ships the approved cultures, artifact order, and required/elective graph', () => {
    const catalog = openingCatalog()
    expect(catalog.source.cultures).toHaveLength(2)
    expect(catalog.source.puzzles).toHaveLength(7)
    expect(catalog.source.performances.length).toBeGreaterThanOrEqual(7)

    const ids = catalog.source.puzzles.map((puzzle) => puzzle.id)
    expect(ids).toEqual(puzzleIds.map(puzzleId))
    expect(isRequired(catalog, puzzleId('two-mark-projection'))).toBe(false)
    for (const id of ids.filter((id) => id !== puzzleId('two-mark-projection'))) {
      expect(isRequired(catalog, id)).toBe(true)
    }

    expect(catalog.source.cultures).toEqual([
      expect.objectContaining({
        id: cultureId('seyric-horizon'), name: 'The Seyric Horizon', relativeAge: 0,
        lineage: [], isolation: 'uncertain', sealingVocabulary: ['veils', 'fields', 'echoes', 'rings', 'marks'],
        unlocksAfter: [], gateway: puzzleId('two-veils'),
      }),
      expect.objectContaining({
        id: cultureId('myratic-tradition'), name: 'The Myratic Tradition', relativeAge: 1,
        lineage: [], isolation: 'isolated', sealingVocabulary: ['hollows', 'patterns'],
        unlocksAfter: [puzzleId('single-mark-return')], gateway: puzzleId('blank-witness'),
      }),
    ])
    expect(catalog.source.puzzles.map((puzzle) => puzzle.prerequisites)).toEqual([
      [], [puzzleId('two-veils')], [puzzleId('four-veils')],
      [puzzleId('forked-veil')], [puzzleId('echoed-veil')],
      [puzzleId('single-mark-return')], [],
    ])
  })

  it('replays every approved witness to canonical blank with the exact rules', () => {
    const catalog = openingCatalog()
    const authority = authorityFor(catalog)
    for (const puzzle of catalog.source.puzzles) {
      let session = startPuzzle(puzzle)
      for (const step of puzzle.witness) {
        session = applyGameStep(session, step, authority).session
      }
      expect(isBlank(currentDiagram(session)), puzzle.id).toBe(true)
    }

    expect(rules('two-veils')).toEqual(['doubleCutElim'])
    expect(rules('four-veils')).toEqual(['doubleCutElim', 'doubleCutElim'])
    expect(rules('forked-veil')).toEqual(['erasure', 'doubleCutElim'])
    expect(rules('echoed-veil')).toEqual(['deiteration', 'erasure', 'doubleCutElim'])
    expect(rules('single-mark-return')).toEqual([
      'deiteration', 'erasure', 'vacuousElim', 'doubleCutElim',
    ])
    expect(rules('two-mark-projection')).toEqual([
      'deiteration', 'erasure', 'erasure', 'vacuousElim', 'vacuousElim', 'doubleCutElim',
    ])
    expect(rules('blank-witness')).toEqual(['comprehensionInstantiate'])
  })

  it('authors the exact closed formulas independently of witness replay', () => {
    expect(puzzleIds.map(structure)).toEqual([
      { sheets: 1, cuts: 2, bubbleArities: [], atomsPerBinder: [], atoms: 0, terms: 0, refs: 0 },
      { sheets: 1, cuts: 4, bubbleArities: [], atomsPerBinder: [], atoms: 0, terms: 0, refs: 0 },
      { sheets: 1, cuts: 3, bubbleArities: [], atomsPerBinder: [], atoms: 0, terms: 0, refs: 0 },
      { sheets: 1, cuts: 4, bubbleArities: [], atomsPerBinder: [], atoms: 0, terms: 0, refs: 0 },
      { sheets: 1, cuts: 2, bubbleArities: [0], atomsPerBinder: [2], atoms: 2, terms: 0, refs: 0 },
      { sheets: 1, cuts: 2, bubbleArities: [0, 0], atomsPerBinder: [1, 2], atoms: 3, terms: 0, refs: 0 },
      { sheets: 1, cuts: 0, bubbleArities: [0], atomsPerBinder: [1], atoms: 1, terms: 0, refs: 0 },
    ])
    for (const puzzle of openingCatalog().source.puzzles) {
      expect(puzzle.goal.boundary, puzzle.id).toEqual([])
    }
  })

  it('pins approved learning roles and every approved teacher intervention', () => {
    const catalog = openingCatalog()
    const performances = catalog.source.performances.map((performance) => performance.id)
    expect(performances).toEqual([
      'release-paired-veils', 'resolve-repeated-veils', 'clear-dark-field',
      'lift-supported-echo', 'trace-single-mark-ownership', 'distinguish-nested-owners',
      'supply-complete-pattern',
    ].map(performanceId))

    const puzzle = (id: typeof puzzleIds[number]) => catalog.puzzle(puzzleId(id))
    expect(puzzle('two-veils').teacher.map(({ trigger, text }) => [trigger.kind, text])).toEqual([
      ['opening', 'The Seyric makers often laid one veil directly inside another. When nothing separates a pair, both may be lifted together.'],
    ])
    expect(puzzle('four-veils').teacher.map(({ trigger, text, recovery }) => [trigger.kind, text, recovery])).toEqual([
      ['opening', 'There are two paired veils here. Either pair may be lifted first.', undefined],
      ['proofState', 'The lever beneath the lens records each state. You may draw it back to compare another route.', undefined],
    ])
    expect(puzzle('forked-veil').teacher.map(({ trigger, text, recovery }) => [trigger.kind, text, recovery])).toEqual([
      ['opening', 'A dark field does not preserve every fragment drawn within it. You may clear away a complete fragment to expose a simpler form.', undefined],
      ['proofState', 'An empty veil is a familiar novice’s trap. Nothing remains inside it to work upon. Draw the lever back to before the clearing.', 'timeline'],
    ])
    expect(puzzle('echoed-veil').teacher.map(({ trigger, text }) => [trigger.kind, text])).toEqual([
      ['opening', 'The inner fragment is an exact echo of the older form outside it. Where the older form remains, the echo may be lifted.'],
      ['stalled', 'Compare the innermost fragment with the form in the surrounding field. The match must be exact.'],
    ])
    expect(puzzle('single-mark-return').teacher.map(({ trigger, text }) => [trigger.kind, text])).toEqual([
      ['opening', 'This colored mark belongs to the ring surrounding it. The veil changes where it appears, not which ring owns it.'],
      ['completion', 'Good. The Seyric rings are ownership marks, not ornament. That distinction will matter among the Myratic finds.'],
    ])
    expect(puzzle('two-mark-projection').teacher.map(({ trigger, text }) => [trigger.kind, text])).toEqual([
      ['stalled', 'Trace each color back to its own ring before removing anything.'],
    ])
    expect(puzzle('blank-witness').teacher.map(({ trigger, text }) => [trigger.kind, text])).toEqual([
      ['opening', 'The Myratic hollow is deliberate. It asks for an entire seal-pattern. Open the loupe and place the blank sheet within it.'],
      ['completion', 'Precisely. To a Myratic seal, even an unwritten sheet is a complete pattern.'],
    ])

    const timelineState = puzzle('four-veils').teacher[1]!.trigger
    expect(timelineState.kind).toBe('proofState')
    if (timelineState.kind === 'proofState') {
      expect(Object.values(timelineState.state.diagram.regions)
        .filter((region) => region.kind === 'cut')).toHaveLength(2)
      expect(timelineState.demonstration.map((step) => step.rule)).toEqual(['doubleCutElim'])
    }

    const emptyVeilTrap = puzzle('forked-veil').teacher[1]!.trigger
    expect(emptyVeilTrap.kind).toBe('proofState')
    if (emptyVeilTrap.kind === 'proofState') {
      expect(Object.values(emptyVeilTrap.state.diagram.regions)
        .filter((region) => region.kind === 'cut')).toHaveLength(1)
      expect(Object.keys(emptyVeilTrap.state.diagram.nodes)).toHaveLength(0)
      expect(Object.keys(emptyVeilTrap.state.diagram.wires)).toHaveLength(0)
      expect(emptyVeilTrap.demonstration.map((step) => step.rule)).toEqual(['erasure'])
    }
  })

  it('preserves the approved professional names and curatorial artifact copy', () => {
    expect(openingCatalog().source.puzzles.map(({ name, provenance }) => ({ name, provenance })))
      .toEqual([
        {
          name: { professional: 'The Seyr Ossuary Seal', curatorShorthand: 'paired-veil form' },
          provenance: {
            summary: 'a basalt stopper recovered in place from Ossuary I at Seyr, the earliest securely excavated intact closure assigned to the horizon.',
            function: 'contained a simple mortuary curse within the burial niche.',
          },
        },
        {
          name: { professional: 'Seyr Cairn Seal IV', curatorShorthand: 'four-veil nesting' },
          provenance: {
            summary: 'the fourth slate closure catalogued from the outer cairn cache at Seyr; tool marks suggest it was cut during one workshop episode.',
            function: 'reinforced a cache curse through repeated nested closure.',
          },
        },
        {
          name: { professional: 'The Orra Gate Fragment', curatorShorthand: 'forked field' },
          provenance: {
            summary: 'a broken limestone lintel ward from the Orra Gate. The forked interior appears to be a later repair or accretion rather than the original carving.',
            function: 'confined a threshold curse while allowing one obstructing fragment to be cleared during licensed passage.',
          },
        },
        {
          name: { professional: 'Tel Vey Chamber Seal VIII', curatorShorthand: 'supported-echo form' },
          provenance: {
            summary: 'the eighth closure recorded in the Tel Vey storage chamber; its repeated inner fragment remains unusually crisp beneath mineral deposits.',
            function: 'reinforced a chamber curse by repeating an older surrounding form inside a deeper field.',
          },
        },
        {
          name: { professional: 'The Auten Reliquary Closure', curatorShorthand: 'single-ring ownership form' },
          provenance: {
            summary: "a bronze-faced reliquary closure from Auten, preserving the first securely dated Seyric ring with a bound colored mark. Its discovery forced a revision of the horizon's chronology.",
            function: 'returned a marked condition through a veiled chamber while keeping both occurrences under one ring.',
          },
        },
        {
          name: {
            professional: 'Seyric Field Seal S-27', curatorShorthand: 'two-ring field form', accession: 'S-27',
          },
          provenance: {
            summary: 'a small repetitive tablet from Seyr workshop refuse, probably a routine exercise or production trial rather than a commissioned closure.',
            function: 'practiced separating two nested owners while retaining only the mark required by the seal.',
          },
        },
        {
          name: { professional: 'The Uninscribed Votive of Myrat', curatorShorthand: 'blank-hollow form' },
          provenance: {
            summary: 'an alabaster votive from the isolated Myrat complex. Wear and residue establish that its empty face is intentional and integral to the seal, not unfinished work or later damage.',
            function: 'required the maker or breaker to supply one complete pattern for its deliberate hollow.',
          },
        },
      ])
  })

  it('returns fresh source structures on every request', () => {
    const first = openingCatalogSource()
    const second = openingCatalogSource()
    expect(second).toEqual(first)
    expect(second).not.toBe(first)
    expect(second.cultures).not.toBe(first.cultures)
    expect(second.performances).not.toBe(first.performances)
    expect(second.puzzles).not.toBe(first.puzzles)
  })
})
