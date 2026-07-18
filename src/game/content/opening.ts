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
  type PerformanceDefinition,
  type PuzzleDefinition,
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

const performances = (): readonly PerformanceDefinition[] => [
  {
    id: RELEASE_PAIRED_VEILS,
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
    id: RESOLVE_REPEATED_VEILS,
    description: 'Resolve a seal containing more than one eligible pair.',
    prerequisites: [RELEASE_PAIRED_VEILS],
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
    id: CLEAR_DARK_FIELD,
    description: 'Clear a complete fragment from an eligible dark field.',
    prerequisites: [RELEASE_PAIRED_VEILS],
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
    id: LIFT_SUPPORTED_ECHO,
    description: 'Lift an exact repeated fragment supported by an older matching form.',
    prerequisites: [CLEAR_DARK_FIELD],
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
    id: TRACE_SINGLE_MARK_OWNERSHIP,
    description: 'Trace one mark through veils to the ring that owns it.',
    prerequisites: [LIFT_SUPPORTED_ECHO],
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
    id: DISTINGUISH_NESTED_OWNERS,
    description: 'Keep marks belonging to nested rings independent.',
    prerequisites: [TRACE_SINGLE_MARK_OWNERSHIP],
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
    id: SUPPLY_COMPLETE_PATTERN,
    description: 'Supply a complete pattern for a Myratic hollow.',
    prerequisites: [TRACE_SINGLE_MARK_OWNERSHIP],
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
    witness: [{ rule: 'doubleCutElim', region: outer }],
    learning: {
      introduces: [RELEASE_PAIRED_VEILS], practices: [], retrieves: [], assesses: [],
      rulesUsed: ['doubleCutElim'],
    },
    teacher: [{
      id: 'opening-paired-veils', performance: RELEASE_PAIRED_VEILS,
      trigger: { kind: 'opening' }, repeat: 'once',
      pages: [
        'Move the pointer over a mark in the seal. A glow appears when the mark can be acted on.',
        'Click a highlighted mark to select it. The selection remains lit after the pointer moves away.',
        'Click a selected mark again to deselect it. Click the empty field to clear the whole selection.',
        'Select the outer boundary of the paired veils. Right-click and choose “Eliminate the double cut,” or press Delete or Backspace, to lift both veils and finish the proof.',
      ],
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
  const teacher = [{
      id: 'opening-repeated-veils', performance: RESOLVE_REPEATED_VEILS,
      trigger: { kind: 'opening' }, repeat: 'once',
      pages: ['There are two paired veils here. Either pair may be lifted first.'],
    }] as const
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
    witness: [eraseSibling, { rule: 'doubleCutElim', region: outer }],
    learning: {
      introduces: [CLEAR_DARK_FIELD], practices: [], retrieves: [RELEASE_PAIRED_VEILS],
      assesses: [], rulesUsed: ['erasure', 'doubleCutElim'],
    },
    teacher: [
      {
        id: 'opening-dark-field', performance: CLEAR_DARK_FIELD,
        trigger: { kind: 'opening' }, repeat: 'once',
        pages: ['A dark field does not preserve every fragment drawn within it. You may clear away a complete fragment to expose a simpler form.'],
      },
      {
        id: 'empty-veil-trap', performance: CLEAR_DARK_FIELD,
        trigger: { kind: 'recognizedUnwinnable', state: trap, demonstration: [eraseCore] }, repeat: 'once',
        recovery: 'timeline',
        pages: ['An empty veil is a familiar novice’s trap. Nothing remains inside it to work upon. Draw the lever back to before the clearing.'],
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
        pages: ['The inner fragment is an exact echo of the older form outside it. Where the older form remains, the echo may be lifted.'],
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
        pages: ['This colored mark belongs to the ring surrounding it. The veil changes where it appears, not which ring owns it.'],
      },
      {
        id: 'completion-single-ring', performance: TRACE_SINGLE_MARK_OWNERSHIP,
        trigger: { kind: 'completion' }, repeat: 'once',
        pages: ['Good. The Seyric rings are ownership marks, not ornament. That distinction will matter among the Myratic finds.'],
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
        CLEAR_DARK_FIELD,
        LIFT_SUPPORTED_ECHO,
        TRACE_SINGLE_MARK_OWNERSHIP,
      ],
      rulesUsed: ['deiteration', 'erasure', 'vacuousElim', 'doubleCutElim'],
    },
    teacher: [],
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
        pages: ['The Myratic hollow is deliberate. It asks for an entire seal-pattern. Open the loupe and place the blank sheet within it.'],
      },
      {
        id: 'completion-blank-hollow', performance: SUPPLY_COMPLETE_PATTERN,
        trigger: { kind: 'completion' }, repeat: 'once',
        pages: ['Precisely. To a Myratic seal, even an unwritten sheet is a complete pattern.'],
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
        shortName: 'Seyric',
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
        shortName: 'Myratic',
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
