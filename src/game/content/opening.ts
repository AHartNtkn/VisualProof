import { DiagramBuilder } from '../../kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import type { Diagram } from '../../kernel/diagram/diagram'
import { mkSelection } from '../../kernel/diagram/subgraph/selection'
import { applyStep, type ProofStep } from '../../kernel/proof/step'
import { buildCatalog, type GameCatalog } from '../catalog'
import {
  cultureId,
  performanceId,
  puzzleId,
  type GameCatalogSource,
  type KnowledgePoint,
  type PerformanceDefinition,
  type PuzzleDefinition,
  type TeacherIntervention,
} from '../types'

const SEYRIC = cultureId('seyric-horizon')
const MYRATIC = cultureId('myratic-tradition')

const RELEASE_PAIRED_VEILS = performanceId('release-paired-veils')
const RESOLVE_REPEATED_VEILS = performanceId('resolve-repeated-veils')
const CLEAR_DARK_FIELD = performanceId('clear-dark-field')
const LIFT_SUPPORTED_ECHO = performanceId('lift-supported-echo')
const TRACE_SINGLE_MARK_OWNERSHIP = performanceId('trace-single-mark-ownership')
const DISTINGUISH_NESTED_OWNERS = performanceId('distinguish-nested-owners')
const SUPPLY_COMPLETE_PATTERN = performanceId('supply-complete-pattern')

const TWO_VEILS = puzzleId('two-veils')
const FOUR_VEILS = puzzleId('four-veils')
const FORKED_VEIL = puzzleId('forked-veil')
const ECHOED_VEIL = puzzleId('echoed-veil')
const SINGLE_MARK_RETURN = puzzleId('single-mark-return')
const TWO_MARK_PROJECTION = puzzleId('two-mark-projection')
const BLANK_WITNESS = puzzleId('blank-witness')

const closed = (builder: DiagramBuilder): DiagramWithBoundary =>
  mkDiagramWithBoundary(builder.build(), [])

const backward = (diagram: Diagram, step: ProofStep): Diagram =>
  applyStep(diagram, step, { theorems: new Map(), relations: new Map() }, 'backward')

const knowledgePoints = (clauses: readonly string[]): readonly KnowledgePoint[] =>
  clauses.map((instruction, index) => ({
    id: `point-${index + 1}`,
    instruction,
    commonError: 'Acts without establishing this condition.',
    correction: `Recheck the seal: ${instruction}`,
  }))

const performance = (
  id: ReturnType<typeof performanceId>,
  description: string,
  prerequisites: readonly ReturnType<typeof performanceId>[],
  clauses: readonly string[],
  masteryEvidence: string,
): PerformanceDefinition => ({
  id,
  description,
  prerequisites,
  knowledgePoints: knowledgePoints(clauses),
  masteryEvidence,
  remediation: [],
})

const performances = (): readonly PerformanceDefinition[] => [
  performance(
    RELEASE_PAIRED_VEILS,
    'Lift one eligible pair of veils without disturbing what it encloses.',
    [],
    [
      'The veils are directly nested.',
      'Nothing lies between their boundaries.',
      'Lifting them preserves enclosed content.',
    ],
    'Independently identifies and lifts an eligible pair.',
  ),
  performance(
    RESOLVE_REPEATED_VEILS,
    'Resolve a seal containing more than one eligible pair.',
    [RELEASE_PAIRED_VEILS],
    [
      'More than one pair may be eligible.',
      'Either legal order may be used.',
      'Lifting one pair may expose another.',
    ],
    'Completes nested-pair practice without treating one valid order as mandatory.',
  ),
  performance(
    CLEAR_DARK_FIELD,
    'Clear a complete fragment from an eligible dark field.',
    [RELEASE_PAIRED_VEILS],
    [
      'Clearing is allowed only in the appropriate field.',
      'The selection must be a complete fragment.',
      'Clearing can expose an older paired form.',
    ],
    'Clears only the necessary fragment and retrieves paired-veiling.',
  ),
  performance(
    LIFT_SUPPORTED_ECHO,
    'Lift an exact repeated fragment supported by an older matching form.',
    [CLEAR_DARK_FIELD],
    [
      'The outer support must already exist.',
      'The echo must match exactly.',
      'Lifting the echo leaves its support in place.',
    ],
    'Distinguishes an exact supported echo from a merely similar fragment.',
  ),
  performance(
    TRACE_SINGLE_MARK_OWNERSHIP,
    'Trace one mark through veils to the ring that owns it.',
    [LIFT_SUPPORTED_ECHO],
    [
      'A ring owns matching marks throughout its interior.',
      'Intervening veils do not change ownership.',
      'A ring dissolves only after it owns no marks.',
    ],
    'Resolves the single-ring artifact while combining all earlier spatial skills.',
  ),
  performance(
    DISTINGUISH_NESTED_OWNERS,
    'Keep marks belonging to nested rings independent.',
    [TRACE_SINGLE_MARK_OWNERSHIP],
    [
      'Each ring owns only its corresponding marks.',
      'Nesting does not merge owners.',
      'Removing one owner’s material must not capture or release another’s marks.',
    ],
    'Independently resolves the elective two-ring artifact.',
  ),
  performance(
    SUPPLY_COMPLETE_PATTERN,
    'Supply a complete pattern for a Myratic hollow.',
    [TRACE_SINGLE_MARK_OWNERSHIP],
    [
      'A hollow may stand for an entire pattern.',
      'The blank sheet is a complete pattern.',
      'Committing the loupe replaces every occurrence consistently.',
    ],
    'Uses the construction loupe to resolve ∃P.P with the blank sheet.',
  ),
]

function twoVeils(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  builder.cut(outer)
  return {
    id: TWO_VEILS,
    culture: SEYRIC,
    name: { professional: 'The Seyr Ossuary Seal', curatorShorthand: 'paired-veil form' },
    provenance: {
      summary: 'a basalt stopper recovered in place from Ossuary I at Seyr, the earliest securely excavated intact closure assigned to the horizon.',
      function: 'contained a simple mortuary curse within the burial niche.',
    },
    goal: closed(builder),
    prerequisites: [],
    grantsVellum: true,
    witness: [{ rule: 'doubleCutElim', region: outer }],
    learning: {
      introduces: [RELEASE_PAIRED_VEILS], practices: [], retrieves: [], assesses: [],
      rulesUsed: ['doubleCutElim'],
    },
    teacher: [{
      id: 'opening-paired-veils', performance: RELEASE_PAIRED_VEILS,
      trigger: { kind: 'opening' }, repeat: 'once',
      text: 'The Seyric makers often laid one veil directly inside another. When nothing separates a pair, both may be lifted together.',
    }],
  }
}

function fourVeils(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const second = builder.cut(outer)
  const third = builder.cut(second)
  builder.cut(third)
  const goal = closed(builder)
  const first: ProofStep = { rule: 'doubleCutElim', region: third }
  const intermediate = mkDiagramWithBoundary(backward(goal.diagram, first), [])
  const teacher: readonly TeacherIntervention[] = [
    {
      id: 'opening-repeated-veils', performance: RESOLVE_REPEATED_VEILS,
      trigger: { kind: 'opening' }, repeat: 'once',
      text: 'There are two paired veils here. Either pair may be lifted first.',
    },
    {
      id: 'timeline-after-first-pair', performance: RESOLVE_REPEATED_VEILS,
      trigger: { kind: 'proofState', state: intermediate, demonstration: [first] }, repeat: 'once',
      text: 'The lever beneath the lens records each state. You may draw it back to compare another route.',
    },
  ]
  return {
    id: FOUR_VEILS,
    culture: SEYRIC,
    name: { professional: 'Seyr Cairn Seal IV', curatorShorthand: 'four-veil nesting' },
    provenance: {
      summary: 'the fourth slate closure catalogued from the outer cairn cache at Seyr; tool marks suggest it was cut during one workshop episode.',
      function: 'reinforced a cache curse through repeated nested closure.',
    },
    goal,
    prerequisites: [TWO_VEILS],
    grantsVellum: true,
    witness: [first, { rule: 'doubleCutElim', region: outer }],
    learning: {
      introduces: [RESOLVE_REPEATED_VEILS], practices: [RELEASE_PAIRED_VEILS],
      retrieves: [], assesses: [RELEASE_PAIRED_VEILS], rulesUsed: ['doubleCutElim'],
    },
    teacher,
  }
}

function forkedVeil(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const kept = builder.cut(outer)
  const removed = builder.cut(outer)
  const goal = closed(builder)
  const eraseSibling: ProofStep = {
    rule: 'erasure',
    sel: mkSelection(goal.diagram, { region: outer, regions: [removed], nodes: [], wires: [] }),
  }
  const eraseCore: ProofStep = {
    rule: 'erasure',
    sel: mkSelection(goal.diagram, { region: outer, regions: [kept, removed], nodes: [], wires: [] }),
  }
  const trap = mkDiagramWithBoundary(backward(goal.diagram, eraseCore), [])
  return {
    id: FORKED_VEIL,
    culture: SEYRIC,
    name: { professional: 'The Orra Gate Fragment', curatorShorthand: 'forked field' },
    provenance: {
      summary: 'a broken limestone lintel ward from the Orra Gate. The forked interior appears to be a later repair or accretion rather than the original carving.',
      function: 'confined a threshold curse while allowing one obstructing fragment to be cleared during licensed passage.',
    },
    goal,
    prerequisites: [FOUR_VEILS],
    grantsVellum: true,
    witness: [eraseSibling, { rule: 'doubleCutElim', region: outer }],
    learning: {
      introduces: [CLEAR_DARK_FIELD], practices: [], retrieves: [RELEASE_PAIRED_VEILS],
      assesses: [], rulesUsed: ['erasure', 'doubleCutElim'],
    },
    teacher: [
      {
        id: 'opening-dark-field', performance: CLEAR_DARK_FIELD,
        trigger: { kind: 'opening' }, repeat: 'once',
        text: 'A dark field does not preserve every fragment drawn within it. You may clear away a complete fragment to expose a simpler form.',
      },
      {
        id: 'empty-veil-trap', performance: CLEAR_DARK_FIELD,
        trigger: { kind: 'proofState', state: trap, demonstration: [eraseCore] }, repeat: 'once',
        recovery: 'timeline',
        text: 'An empty veil is a familiar novice’s trap. Nothing remains inside it to work upon. Draw the lever back to before the clearing.',
      },
    ],
  }
}

function echoedVeil(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const support = builder.cut(outer)
  const deeperField = builder.cut(outer)
  const echo = builder.cut(deeperField)
  const goal = closed(builder)
  const deiterate: ProofStep = {
    rule: 'deiteration',
    sel: mkSelection(goal.diagram, { region: deeperField, regions: [echo], nodes: [], wires: [] }),
    fuel: 100,
  }
  const afterDeiteration = backward(goal.diagram, deiterate)
  const eraseSupport: ProofStep = {
    rule: 'erasure',
    sel: mkSelection(afterDeiteration, { region: outer, regions: [support], nodes: [], wires: [] }),
  }
  return {
    id: ECHOED_VEIL,
    culture: SEYRIC,
    name: { professional: 'Tel Vey Chamber Seal VIII', curatorShorthand: 'supported-echo form' },
    provenance: {
      summary: 'the eighth closure recorded in the Tel Vey storage chamber; its repeated inner fragment remains unusually crisp beneath mineral deposits.',
      function: 'reinforced a chamber curse by repeating an older surrounding form inside a deeper field.',
    },
    goal,
    prerequisites: [FORKED_VEIL],
    grantsVellum: true,
    witness: [deiterate, eraseSupport, { rule: 'doubleCutElim', region: outer }],
    learning: {
      introduces: [LIFT_SUPPORTED_ECHO], practices: [CLEAR_DARK_FIELD],
      retrieves: [RELEASE_PAIRED_VEILS], assesses: [],
      rulesUsed: ['deiteration', 'erasure', 'doubleCutElim'],
    },
    teacher: [
      {
        id: 'opening-supported-echo', performance: LIFT_SUPPORTED_ECHO,
        trigger: { kind: 'opening' }, repeat: 'once',
        text: 'The inner fragment is an exact echo of the older form outside it. Where the older form remains, the echo may be lifted.',
      },
      {
        id: 'stalled-supported-echo', performance: LIFT_SUPPORTED_ECHO,
        trigger: { kind: 'stalled', level: 1 }, repeat: 'once',
        text: 'Compare the innermost fragment with the form in the surrounding field. The match must be exact.',
      },
    ],
  }
}

function singleMarkReturn(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const ring = builder.bubble(outer, 0)
  const premise = builder.atom(ring, ring)
  const conclusionVeil = builder.cut(ring)
  const conclusion = builder.atom(conclusionVeil, ring)
  const goal = closed(builder)
  const deiterate: ProofStep = {
    rule: 'deiteration',
    sel: mkSelection(goal.diagram, { region: conclusionVeil, regions: [], nodes: [conclusion], wires: [] }),
    fuel: 100,
  }
  const afterDeiteration = backward(goal.diagram, deiterate)
  const erasePremise: ProofStep = {
    rule: 'erasure',
    sel: mkSelection(afterDeiteration, { region: ring, regions: [], nodes: [premise], wires: [] }),
  }
  return {
    id: SINGLE_MARK_RETURN,
    culture: SEYRIC,
    name: { professional: 'The Auten Reliquary Closure', curatorShorthand: 'single-ring ownership form' },
    provenance: {
      summary: "a bronze-faced reliquary closure from Auten, preserving the first securely dated Seyric ring with a bound colored mark. Its discovery forced a revision of the horizon's chronology.",
      function: 'returned a marked condition through a veiled chamber while keeping both occurrences under one ring.',
    },
    goal,
    prerequisites: [ECHOED_VEIL],
    grantsVellum: true,
    witness: [
      deiterate,
      erasePremise,
      { rule: 'vacuousElim', region: ring },
      { rule: 'doubleCutElim', region: outer },
    ],
    learning: {
      introduces: [TRACE_SINGLE_MARK_OWNERSHIP],
      practices: [LIFT_SUPPORTED_ECHO, CLEAR_DARK_FIELD],
      retrieves: [RELEASE_PAIRED_VEILS], assesses: [],
      rulesUsed: ['deiteration', 'erasure', 'vacuousElim', 'doubleCutElim'],
    },
    teacher: [
      {
        id: 'opening-single-ring', performance: TRACE_SINGLE_MARK_OWNERSHIP,
        trigger: { kind: 'opening' }, repeat: 'once',
        text: 'This colored mark belongs to the ring surrounding it. The veil changes where it appears, not which ring owns it.',
      },
      {
        id: 'completion-single-ring', performance: TRACE_SINGLE_MARK_OWNERSHIP,
        trigger: { kind: 'completion' }, repeat: 'once',
        text: 'Good. The Seyric rings are ownership marks, not ornament. That distinction will matter among the Myratic finds.',
      },
    ],
  }
}

function twoMarkProjection(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const pRing = builder.bubble(outer, 0)
  const qRing = builder.bubble(pRing, 0)
  const pPremise = builder.atom(qRing, pRing)
  const qPremise = builder.atom(qRing, qRing)
  const conclusionVeil = builder.cut(qRing)
  const pConclusion = builder.atom(conclusionVeil, pRing)
  const goal = closed(builder)
  const deiterate: ProofStep = {
    rule: 'deiteration',
    sel: mkSelection(goal.diagram, { region: conclusionVeil, regions: [], nodes: [pConclusion], wires: [] }),
    fuel: 100,
  }
  const afterDeiteration = backward(goal.diagram, deiterate)
  const eraseQ: ProofStep = {
    rule: 'erasure',
    sel: mkSelection(afterDeiteration, { region: qRing, regions: [], nodes: [qPremise], wires: [] }),
  }
  const afterEraseQ = backward(afterDeiteration, eraseQ)
  const eraseP: ProofStep = {
    rule: 'erasure',
    sel: mkSelection(afterEraseQ, { region: qRing, regions: [], nodes: [pPremise], wires: [] }),
  }
  return {
    id: TWO_MARK_PROJECTION,
    culture: SEYRIC,
    name: {
      professional: 'Seyric Field Seal S-27', curatorShorthand: 'two-ring field form', accession: 'S-27',
    },
    provenance: {
      summary: 'a small repetitive tablet from Seyr workshop refuse, probably a routine exercise or production trial rather than a commissioned closure.',
      function: 'practiced separating two nested owners while retaining only the mark required by the seal.',
    },
    goal,
    prerequisites: [SINGLE_MARK_RETURN],
    grantsVellum: true,
    witness: [
      deiterate,
      eraseQ,
      eraseP,
      { rule: 'vacuousElim', region: qRing },
      { rule: 'vacuousElim', region: pRing },
      { rule: 'doubleCutElim', region: outer },
    ],
    learning: {
      introduces: [DISTINGUISH_NESTED_OWNERS], practices: [TRACE_SINGLE_MARK_OWNERSHIP],
      retrieves: [],
      assesses: [
        RELEASE_PAIRED_VEILS,
        RESOLVE_REPEATED_VEILS,
        CLEAR_DARK_FIELD,
        LIFT_SUPPORTED_ECHO,
        TRACE_SINGLE_MARK_OWNERSHIP,
      ],
      rulesUsed: ['deiteration', 'erasure', 'vacuousElim', 'doubleCutElim'],
    },
    teacher: [{
      id: 'stalled-nested-rings', performance: DISTINGUISH_NESTED_OWNERS,
      trigger: { kind: 'stalled', level: 1 }, repeat: 'once',
      text: 'Trace each color back to its own ring before removing anything.',
    }],
  }
}

function blankWitness(): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const hollow = builder.bubble(builder.root, 0)
  builder.atom(hollow, hollow)
  const blank = closed(new DiagramBuilder())
  return {
    id: BLANK_WITNESS,
    culture: MYRATIC,
    name: { professional: 'The Uninscribed Votive of Myrat', curatorShorthand: 'blank-hollow form' },
    provenance: {
      summary: 'an alabaster votive from the isolated Myrat complex. Wear and residue establish that its empty face is intentional and integral to the seal, not unfinished work or later damage.',
      function: 'required the maker or breaker to supply one complete pattern for its deliberate hollow.',
    },
    goal: closed(builder),
    prerequisites: [],
    grantsVellum: true,
    witness: [{
      rule: 'comprehensionInstantiate', bubble: hollow, comp: blank,
      attachments: [], binders: {},
    }],
    learning: {
      introduces: [SUPPLY_COMPLETE_PATTERN], practices: [],
      retrieves: [TRACE_SINGLE_MARK_OWNERSHIP], assesses: [],
      rulesUsed: ['comprehensionInstantiate'],
    },
    teacher: [
      {
        id: 'opening-blank-hollow', performance: SUPPLY_COMPLETE_PATTERN,
        trigger: { kind: 'opening' }, repeat: 'once',
        text: 'The Myratic hollow is deliberate. It asks for an entire seal-pattern. Open the loupe and place the blank sheet within it.',
      },
      {
        id: 'completion-blank-hollow', performance: SUPPLY_COMPLETE_PATTERN,
        trigger: { kind: 'completion' }, repeat: 'once',
        text: 'Precisely. To a Myratic seal, even an unwritten sheet is a complete pattern.',
      },
    ],
  }
}

export function openingCatalogSource(): GameCatalogSource {
  return {
    cultures: [
      {
        id: SEYRIC,
        name: 'The Seyric Horizon',
        relativeAge: 0,
        historicalSummary: 'the earliest secure sealing horizon, known from funerary closures, threshold wards, and stone stoppers. Its self-name is unknown; “Seyric” is the modern archaeological exonym.',
        lineage: [],
        isolation: 'uncertain',
        sealingVocabulary: ['veils', 'fields', 'echoes', 'rings', 'marks'],
        unlocksAfter: [],
        gateway: TWO_VEILS,
      },
      {
        id: MYRATIC,
        name: 'The Myratic Tradition',
        relativeAge: 1,
        historicalSummary: 'the isolated Myrat complex, whose deliberate hollows may stand for complete seal-patterns. No direct Seyric lineage is established. Supplying a pattern is its first technique, not the identity of the whole tradition.',
        lineage: [],
        isolation: 'isolated',
        sealingVocabulary: ['hollows', 'patterns'],
        unlocksAfter: [SINGLE_MARK_RETURN],
        gateway: BLANK_WITNESS,
      },
    ],
    performances: performances(),
    puzzles: [
      twoVeils(),
      fourVeils(),
      forkedVeil(),
      echoedVeil(),
      singleMarkReturn(),
      twoMarkProjection(),
      blankWitness(),
    ],
    context: { relations: new Map() },
  }
}

export const openingCatalog = (): GameCatalog => buildCatalog(openingCatalogSource())
