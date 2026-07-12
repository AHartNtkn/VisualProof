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

const expectedPerformances = [
  {
    id: performanceId('release-paired-veils'),
    description: 'Lift one eligible pair of veils without disturbing what it encloses.',
    prerequisites: [],
    knowledgePoints: [
      {
        id: 'recognize-direct-nesting',
        instruction: 'The veils are directly nested.',
        commonError: 'Pairs veils that are not directly nested.',
        correction: 'Choose two veils whose boundaries are directly nested.',
      },
      {
        id: 'check-empty-annulus',
        instruction: 'Nothing lies between their boundaries.',
        commonError: 'Treats separated boundaries as an eligible pair.',
        correction: 'Confirm that nothing lies between the two boundaries.',
      },
      {
        id: 'preserve-enclosed-content',
        instruction: 'Lifting them preserves enclosed content.',
        commonError: 'Removes or changes content enclosed by the inner veil.',
        correction: 'Lift only the paired boundaries and preserve everything they enclose.',
      },
    ],
    masteryEvidence: 'Independently identifies and lifts an eligible pair.',
    remediation: [],
  },
  {
    id: performanceId('resolve-repeated-veils'),
    description: 'Resolve a seal containing more than one eligible pair.',
    prerequisites: [performanceId('release-paired-veils')],
    knowledgePoints: [
      {
        id: 'recognize-multiple-pairs',
        instruction: 'More than one pair may be eligible.',
        commonError: 'Stops after finding the first eligible pair.',
        correction: 'Scan the whole seal for every directly nested eligible pair.',
      },
      {
        id: 'allow-either-order',
        instruction: 'Either legal order may be used.',
        commonError: 'Treats one legal pair as the mandatory first move.',
        correction: 'Choose either currently eligible pair; neither legal order is privileged.',
      },
      {
        id: 'recheck-after-lifting',
        instruction: 'Lifting one pair may expose another.',
        commonError: 'Does not inspect the new state after lifting a pair.',
        correction: 'Recheck the resulting seal for a newly exposed eligible pair.',
      },
    ],
    masteryEvidence: 'Completes nested-pair practice without treating one valid order as mandatory.',
    remediation: [],
  },
  {
    id: performanceId('clear-dark-field'),
    description: 'Clear a complete fragment from an eligible dark field.',
    prerequisites: [performanceId('release-paired-veils')],
    knowledgePoints: [
      {
        id: 'check-clearing-field',
        instruction: 'Clearing is allowed only in the appropriate field.',
        commonError: 'Attempts to clear a fragment from an ineligible field.',
        correction: 'Trace the fragment to a field where clearing is allowed.',
      },
      {
        id: 'select-complete-fragment',
        instruction: 'The selection must be a complete fragment.',
        commonError: 'Selects only part of a fragment.',
        correction: 'Select the whole fragment, including every boundary and mark it contains.',
      },
      {
        id: 'anticipate-exposed-pair',
        instruction: 'Clearing can expose an older paired form.',
        commonError: 'Misses the paired form revealed by clearing.',
        correction: 'Inspect the cleared field for an older pair of directly nested veils.',
      },
    ],
    masteryEvidence: 'Clears only the necessary fragment and retrieves paired-veiling.',
    remediation: [],
  },
  {
    id: performanceId('lift-supported-echo'),
    description: 'Lift an exact repeated fragment supported by an older matching form.',
    prerequisites: [performanceId('clear-dark-field')],
    knowledgePoints: [
      {
        id: 'find-outer-support',
        instruction: 'The outer support must already exist.',
        commonError: 'Treats an unsupported inner fragment as an echo.',
        correction: 'First locate the older matching fragment in a surrounding field.',
      },
      {
        id: 'require-exact-match',
        instruction: 'The echo must match exactly.',
        commonError: 'Accepts a merely similar fragment as an echo.',
        correction: 'Compare the complete fragments and require an exact structural match.',
      },
      {
        id: 'retain-outer-support',
        instruction: 'Lifting the echo leaves its support in place.',
        commonError: 'Removes the older supporting form with its echo.',
        correction: 'Lift only the repeated inner fragment and leave the outer support intact.',
      },
    ],
    masteryEvidence: 'Distinguishes an exact supported echo from a merely similar fragment.',
    remediation: [],
  },
  {
    id: performanceId('trace-single-mark-ownership'),
    description: 'Trace one mark through veils to the ring that owns it.',
    prerequisites: [performanceId('lift-supported-echo')],
    knowledgePoints: [
      {
        id: 'trace-ring-interior',
        instruction: 'A ring owns matching marks throughout its interior.',
        commonError: 'Treats a matching interior mark as unowned.',
        correction: 'Trace the mark outward through the ring’s entire interior to its owning ring.',
      },
      {
        id: 'preserve-owner-through-veils',
        instruction: 'Intervening veils do not change ownership.',
        commonError: 'Assigns a new owner when a mark crosses a veil.',
        correction: 'Continue tracing through intervening veils to the same surrounding ring.',
      },
      {
        id: 'dissolve-only-empty-ring',
        instruction: 'A ring dissolves only after it owns no marks.',
        commonError: 'Attempts to dissolve a ring that still owns a mark.',
        correction: 'Remove every mark owned by the ring before dissolving it.',
      },
    ],
    masteryEvidence: 'Resolves the single-ring artifact while combining all earlier spatial skills.',
    remediation: [],
  },
  {
    id: performanceId('distinguish-nested-owners'),
    description: 'Keep marks belonging to nested rings independent.',
    prerequisites: [performanceId('trace-single-mark-ownership')],
    knowledgePoints: [
      {
        id: 'match-mark-to-own-ring',
        instruction: 'Each ring owns only its corresponding marks.',
        commonError: 'Assigns a mark to the wrong surrounding ring.',
        correction: 'Match each mark to its corresponding ring before changing the seal.',
      },
      {
        id: 'keep-nested-owners-distinct',
        instruction: 'Nesting does not merge owners.',
        commonError: 'Treats nested rings as one owner.',
        correction: 'Track each nested ring as an independent owner.',
      },
      {
        id: 'preserve-other-owner',
        instruction: 'Removing one owner’s material must not capture or release another’s marks.',
        commonError: 'Changes another ring’s marks while removing one owner’s material.',
        correction: 'Remove only material owned by the selected ring and preserve every other ownership relation.',
      },
    ],
    masteryEvidence: 'Independently resolves the elective two-ring artifact.',
    remediation: [],
  },
  {
    id: performanceId('supply-complete-pattern'),
    description: 'Supply a complete pattern for a Myratic hollow.',
    prerequisites: [performanceId('trace-single-mark-ownership')],
    knowledgePoints: [
      {
        id: 'treat-hollow-as-whole-pattern',
        instruction: 'A hollow may stand for an entire pattern.',
        commonError: 'Treats the hollow as a place for only one fragment.',
        correction: 'Construct one complete seal-pattern for the hollow.',
      },
      {
        id: 'recognize-blank-pattern',
        instruction: 'The blank sheet is a complete pattern.',
        commonError: 'Rejects the blank sheet because it contains no marks.',
        correction: 'Use the blank sheet as a complete zero-mark pattern.',
      },
      {
        id: 'replace-occurrences-consistently',
        instruction: 'Committing the loupe replaces every occurrence consistently.',
        commonError: 'Expects the supplied pattern to replace only one occurrence.',
        correction: 'Commit one pattern for every occurrence owned by the hollow’s ring.',
      },
    ],
    masteryEvidence: 'Uses the construction loupe to resolve ∃P.P with the blank sheet.',
    remediation: [],
  },
]

describe('permanent opening catalog', () => {
  it('ships the approved cultures, artifact order, and required/elective graph', () => {
    const catalog = openingCatalog()
    expect(catalog.source.cultures).toHaveLength(2)
    expect(catalog.source.puzzles).toHaveLength(7)
    expect(catalog.source.performances).toHaveLength(7)

    const ids = catalog.source.puzzles.map((puzzle) => puzzle.id)
    expect(ids).toEqual(puzzleIds.map(puzzleId))
    expect(isRequired(catalog, puzzleId('two-mark-projection'))).toBe(false)
    for (const id of ids.filter((id) => id !== puzzleId('two-mark-projection'))) {
      expect(isRequired(catalog, id)).toBe(true)
    }

    expect(catalog.source.cultures).toEqual([
      {
        id: cultureId('seyric-horizon'), name: 'The Seyric Horizon', relativeAge: 0,
        historicalSummary: 'the earliest secure sealing horizon, known from funerary closures, threshold wards, and stone stoppers. Its self-name is unknown; “Seyric” is the modern archaeological exonym.',
        lineage: [], isolation: 'uncertain', sealingVocabulary: ['veils', 'fields', 'echoes', 'rings', 'marks'],
        unlocksAfter: [], gateway: puzzleId('two-veils'),
      },
      {
        id: cultureId('myratic-tradition'), name: 'The Myratic Tradition', relativeAge: 1,
        historicalSummary: 'the isolated Myrat complex, whose deliberate hollows may stand for complete seal-patterns. No direct Seyric lineage is established. Supplying a pattern is its first technique, not the identity of the whole tradition.',
        lineage: [], isolation: 'isolated', sealingVocabulary: ['hollows', 'patterns'],
        unlocksAfter: [puzzleId('single-mark-return')], gateway: puzzleId('blank-witness'),
      },
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
    const source = openingCatalogSource()
    const goal = (id: typeof puzzleIds[number]) =>
      source.puzzles.find((puzzle) => puzzle.id === puzzleId(id))!.goal
    const diagram = (id: typeof puzzleIds[number]) => goal(id).diagram

    expect(diagram('two-veils').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
      r2: { kind: 'cut', parent: 'r1' },
    })
    expect(diagram('four-veils').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
      r2: { kind: 'cut', parent: 'r1' },
      r3: { kind: 'cut', parent: 'r2' },
      r4: { kind: 'cut', parent: 'r3' },
    })
    expect(diagram('forked-veil').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
      r2: { kind: 'cut', parent: 'r1' },
      r3: { kind: 'cut', parent: 'r1' },
    })
    expect(diagram('echoed-veil').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
      r2: { kind: 'cut', parent: 'r1' },
      r3: { kind: 'cut', parent: 'r1' },
      r4: { kind: 'cut', parent: 'r3' },
    })
    expect(diagram('single-mark-return').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
      r2: { kind: 'bubble', parent: 'r1', arity: 0 },
      r3: { kind: 'cut', parent: 'r2' },
    })
    expect(diagram('single-mark-return').nodes).toEqual({
      n0: { kind: 'atom', region: 'r2', binder: 'r2' },
      n1: { kind: 'atom', region: 'r3', binder: 'r2' },
    })
    expect(diagram('two-mark-projection').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'cut', parent: 'r0' },
      r2: { kind: 'bubble', parent: 'r1', arity: 0 },
      r3: { kind: 'bubble', parent: 'r2', arity: 0 },
      r4: { kind: 'cut', parent: 'r3' },
    })
    expect(diagram('two-mark-projection').nodes).toEqual({
      n0: { kind: 'atom', region: 'r3', binder: 'r2' },
      n1: { kind: 'atom', region: 'r3', binder: 'r3' },
      n2: { kind: 'atom', region: 'r4', binder: 'r2' },
    })
    expect(diagram('blank-witness').regions).toEqual({
      r0: { kind: 'sheet' },
      r1: { kind: 'bubble', parent: 'r0', arity: 0 },
    })
    expect(diagram('blank-witness').nodes).toEqual({
      n0: { kind: 'atom', region: 'r1', binder: 'r1' },
    })

    for (const id of puzzleIds) {
      const artifactGoal = goal(id)
      expect(artifactGoal.boundary, id).toEqual([])
      expect(Object.values(artifactGoal.diagram.nodes)
        .some((node) => node.kind === 'term'), id).toBe(false)
      expect(Object.values(artifactGoal.diagram.nodes)
        .some((node) => node.kind === 'ref'), id).toBe(false)
      expect(artifactGoal.diagram.wires, id).toEqual({})
    }
  })

  it('pins approved learning roles and every approved teacher intervention', () => {
    const catalog = openingCatalog()
    expect(catalog.source.performances).toEqual(expectedPerformances)

    expect(catalog.source.puzzles.map((puzzle) => puzzle.learning)).toEqual([
      {
        introduces: [performanceId('release-paired-veils')],
        practices: [], retrieves: [], assesses: [], rulesUsed: ['doubleCutElim'],
      },
      {
        introduces: [performanceId('resolve-repeated-veils')],
        practices: [performanceId('release-paired-veils')], retrieves: [],
        assesses: [performanceId('release-paired-veils')], rulesUsed: ['doubleCutElim'],
      },
      {
        introduces: [performanceId('clear-dark-field')], practices: [],
        retrieves: [performanceId('release-paired-veils')], assesses: [],
        rulesUsed: ['erasure', 'doubleCutElim'],
      },
      {
        introduces: [performanceId('lift-supported-echo')],
        practices: [performanceId('clear-dark-field')],
        retrieves: [performanceId('release-paired-veils')], assesses: [],
        rulesUsed: ['deiteration', 'erasure', 'doubleCutElim'],
      },
      {
        introduces: [performanceId('trace-single-mark-ownership')],
        practices: [performanceId('lift-supported-echo'), performanceId('clear-dark-field')],
        retrieves: [performanceId('release-paired-veils')], assesses: [],
        rulesUsed: ['deiteration', 'erasure', 'vacuousElim', 'doubleCutElim'],
      },
      {
        introduces: [performanceId('distinguish-nested-owners')],
        practices: [performanceId('trace-single-mark-ownership')], retrieves: [],
        assesses: [
          performanceId('release-paired-veils'), performanceId('clear-dark-field'),
          performanceId('lift-supported-echo'),
          performanceId('trace-single-mark-ownership'),
        ],
        rulesUsed: ['deiteration', 'erasure', 'vacuousElim', 'doubleCutElim'],
      },
      {
        introduces: [performanceId('supply-complete-pattern')], practices: [],
        retrieves: [performanceId('trace-single-mark-ownership')], assesses: [],
        rulesUsed: ['comprehensionInstantiate'],
      },
    ])

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
    expect(second.context).not.toBe(first.context)
    expect(second.context.relations).not.toBe(first.context.relations)
    expect(second.cultures[0]!.lineage).not.toBe(first.cultures[0]!.lineage)
    expect(second.cultures[0]!.sealingVocabulary).not.toBe(first.cultures[0]!.sealingVocabulary)
    expect(second.cultures[1]!.unlocksAfter).not.toBe(first.cultures[1]!.unlocksAfter)
    expect(second.performances[1]!.prerequisites).not.toBe(first.performances[1]!.prerequisites)
    expect(second.performances[0]!.knowledgePoints).not.toBe(first.performances[0]!.knowledgePoints)
    expect(second.performances[0]!.knowledgePoints[0])
      .not.toBe(first.performances[0]!.knowledgePoints[0])
    expect(second.puzzles[0]!.goal).not.toBe(first.puzzles[0]!.goal)
    expect(second.puzzles[0]!.goal.diagram).not.toBe(first.puzzles[0]!.goal.diagram)
    expect(second.puzzles[0]!.goal.diagram.regions).not.toBe(first.puzzles[0]!.goal.diagram.regions)
    expect(second.puzzles[4]!.goal.diagram.nodes).not.toBe(first.puzzles[4]!.goal.diagram.nodes)
    expect(second.puzzles[0]!.witness).not.toBe(first.puzzles[0]!.witness)
    expect(second.puzzles[0]!.witness[0]).not.toBe(first.puzzles[0]!.witness[0])
    const firstErasure = first.puzzles[2]!.witness[0]!
    const secondErasure = second.puzzles[2]!.witness[0]!
    expect(firstErasure.rule).toBe('erasure')
    expect(secondErasure.rule).toBe('erasure')
    if (firstErasure.rule === 'erasure' && secondErasure.rule === 'erasure') {
      expect(secondErasure.sel).not.toBe(firstErasure.sel)
      expect(secondErasure.sel.regions).not.toBe(firstErasure.sel.regions)
      expect(secondErasure.sel.nodes).not.toBe(firstErasure.sel.nodes)
      expect(secondErasure.sel.wires).not.toBe(firstErasure.sel.wires)
    }
    expect(second.puzzles[1]!.teacher).not.toBe(first.puzzles[1]!.teacher)
    expect(second.puzzles[1]!.teacher[1]).not.toBe(first.puzzles[1]!.teacher[1])
    expect(second.puzzles[1]!.teacher[1]!.trigger).not.toBe(first.puzzles[1]!.teacher[1]!.trigger)
    const firstProofState = first.puzzles[1]!.teacher[1]!.trigger
    const secondProofState = second.puzzles[1]!.teacher[1]!.trigger
    expect(firstProofState.kind).toBe('proofState')
    expect(secondProofState.kind).toBe('proofState')
    if (firstProofState.kind === 'proofState' && secondProofState.kind === 'proofState') {
      expect(secondProofState.state).not.toBe(firstProofState.state)
      expect(secondProofState.state.diagram).not.toBe(firstProofState.state.diagram)
      expect(secondProofState.demonstration).not.toBe(firstProofState.demonstration)
      expect(secondProofState.demonstration[0]).not.toBe(firstProofState.demonstration[0])
    }
    expect(second.puzzles[0]!.learning).not.toBe(first.puzzles[0]!.learning)
    expect(second.puzzles[0]!.learning.introduces).not.toBe(first.puzzles[0]!.learning.introduces)
    expect(second.puzzles[4]!.learning.practices).not.toBe(first.puzzles[4]!.learning.practices)
    expect(second.puzzles[4]!.learning.retrieves).not.toBe(first.puzzles[4]!.learning.retrieves)
    expect(second.puzzles[5]!.learning.assesses).not.toBe(first.puzzles[5]!.learning.assesses)
    expect(second.puzzles[0]!.learning.rulesUsed).not.toBe(first.puzzles[0]!.learning.rulesUsed)
  })
})
