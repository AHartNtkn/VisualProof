import { boundaryForm } from '../../kernel/diagram/canonical/explore'
import { DiagramError } from '../../kernel/diagram/diagram'
import type { Diagram, NodeId, RegionId } from '../../kernel/diagram/diagram'
import { extractSubgraph } from '../../kernel/diagram/subgraph/extract'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { GameStep } from '../types'

export type SeyricStartViolationCode =
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

export type SeyricStartViolation = {
  readonly code: SeyricStartViolationCode
  readonly detail: string
}

export type SeyricStartAnalysis = {
  readonly ok: boolean
  readonly goalCut: RegionId | null
  readonly prefix: readonly RegionId[]
  readonly matrixRoot: RegionId | null
  readonly violations: readonly SeyricStartViolation[]
}

export type SeyricWitnessViolation = {
  readonly code: 'invalid-start' | 'nonterminal-quantifier-operation' | 'terminal-cleanup'
  readonly detail: string
}

export type SeyricWitnessAudit = {
  readonly ok: boolean
  readonly violations: readonly SeyricWitnessViolation[]
}

const directRegions = (diagram: Diagram, parent: RegionId): readonly RegionId[] =>
  Object.entries(diagram.regions)
    .filter(([, region]) => region.kind !== 'sheet' && region.parent === parent)
    .map(([id]) => id)

const directNodes = (diagram: Diagram, region: RegionId): readonly string[] =>
  Object.entries(diagram.nodes)
    .filter(([, node]) => node.region === region)
    .map(([id]) => id)

const ancestryIncludes = (diagram: Diagram, ancestor: RegionId, member: RegionId): boolean => {
  let current = member
  for (;;) {
    if (current === ancestor) return true
    const region = diagram.regions[current]
    if (region === undefined || region.kind === 'sheet') return false
    current = region.parent
  }
}

/**
 * Analyze the authored start grammar of one Seyric problem.
 *
 * The root contains exactly one ordinary goal cut. Immediately inside that
 * cut there may be one unbroken chain of arity-zero proposition binders. The
 * chain ends as soon as matrix content begins, and no bubble may occur below
 * that point. This is an authored-content constraint, not a restriction on
 * the proof rules available to a player.
 */
export function analyzeSeyricStart(diagram: Diagram): SeyricStartAnalysis {
  const violations: SeyricStartViolation[] = []
  let regionTreeValid = true
  const root = diagram.regions[diagram.root]
  if (root === undefined || root.kind !== 'sheet') {
    violations.push({
      code: 'diagram-structure',
      detail: `diagram root '${diagram.root}' must exist and be the sheet`,
    })
    regionTreeValid = false
  }

  for (const [id, region] of Object.entries(diagram.regions)) {
    if (region.kind === 'sheet') {
      if (id !== diagram.root) {
        violations.push({
          code: 'diagram-structure',
          detail: `region '${id}' is a second sheet rather than a member of root '${diagram.root}'`,
        })
        regionTreeValid = false
      }
      continue
    }
    if (diagram.regions[region.parent] === undefined) {
      violations.push({
        code: 'diagram-structure',
        detail: `region '${id}' has missing parent '${region.parent}'`,
      })
      regionTreeValid = false
    }
  }

  for (const id of Object.keys(diagram.regions)) {
    const seen = new Set<RegionId>()
    let current = id
    for (;;) {
      if (seen.has(current)) {
        violations.push({
          code: 'diagram-structure',
          detail: `region ownership from '${id}' contains a cycle at '${current}'`,
        })
        regionTreeValid = false
        break
      }
      seen.add(current)
      const region = diagram.regions[current]
      if (region === undefined) break
      if (region.kind === 'sheet') {
        if (current !== diagram.root) regionTreeValid = false
        break
      }
      current = region.parent
    }
  }

  for (const [id, node] of Object.entries(diagram.nodes)) {
    if (diagram.regions[node.region] === undefined) {
      violations.push(node.kind === 'atom'
        ? { code: 'atom-region', detail: `atom '${id}' has missing region '${node.region}'` }
        : { code: 'diagram-structure', detail: `node '${id}' has missing region '${node.region}'` })
    }
    if (node.kind === 'atom') {
      const binder = diagram.regions[node.binder]
      if (binder === undefined || binder.kind !== 'bubble') {
        violations.push({
          code: 'atom-binder',
          detail: `atom '${id}' binder '${node.binder}' is not an existing bubble`,
        })
      }
    }
  }

  if (!regionTreeValid) {
    return {
      ok: false,
      goalCut: null,
      prefix: [],
      matrixRoot: null,
      violations,
    }
  }

  const rootRegions = directRegions(diagram, diagram.root)
  const rootNodes = directNodes(diagram, diagram.root)
  const goalCandidate = rootRegions.length === 1 ? rootRegions[0]! : null
  const goalCut = goalCandidate !== null && diagram.regions[goalCandidate]?.kind === 'cut'
    ? goalCandidate
    : null

  if (goalCut === null || rootNodes.length > 0) {
    violations.push({
      code: 'outer-goal',
      detail: 'the sheet must contain exactly one ordinary outer goal cut and no direct matrix content',
    })
  }

  const prefix: RegionId[] = []
  let matrixRoot: RegionId | null = goalCut
  if (goalCut !== null) {
    let current = goalCut
    for (;;) {
      const children = directRegions(diagram, current)
      const bubbles = children.filter((id) => diagram.regions[id]?.kind === 'bubble')
      if (bubbles.length === 0) {
        matrixRoot = current
        break
      }
      if (bubbles.length > 1) {
        violations.push({
          code: 'branched-prefix',
          detail: `region '${current}' branches into proposition binders ${bubbles.map((id) => `'${id}'`).join(', ')}`,
        })
        matrixRoot = current
        break
      }

      const bubble = bubbles[0]!
      const competingRegions = children.filter((id) => id !== bubble)
      const competingNodes = directNodes(diagram, current)
      if (competingRegions.length > 0 || competingNodes.length > 0) {
        violations.push({
          code: 'interrupted-prefix',
          detail: `binder '${bubble}' appears after matrix content has begun in region '${current}'`,
        })
        matrixRoot = current
        break
      }

      const value = diagram.regions[bubble]!
      if (value.kind !== 'bubble') throw new Error('Seyric prefix analysis lost its bubble candidate')
      if (value.arity !== 0) {
        violations.push({
          code: 'prefix-arity',
          detail: `prefix bubble '${bubble}' has arity ${value.arity}; Seyric proposition binders have arity zero`,
        })
      }
      prefix.push(bubble)
      current = bubble
    }
  }

  const prefixSet = new Set(prefix)
  for (const [id, region] of Object.entries(diagram.regions)) {
    if (region.kind === 'bubble' && !prefixSet.has(id)) {
      violations.push({
        code: 'matrix-bubble',
        detail: `bubble '${id}' occurs inside the quantifier-free propositional matrix`,
      })
    }
  }
  for (const [id, node] of Object.entries(diagram.nodes)) {
    if (node.kind !== 'atom') {
      violations.push({
        code: 'non-propositional-node',
        detail: `matrix node '${id}' has kind '${node.kind}' rather than a proposition atom`,
      })
      continue
    }
    if (
      matrixRoot !== null
      && diagram.regions[node.region] !== undefined
      && !ancestryIncludes(diagram, matrixRoot, node.region)
    ) {
      violations.push({
        code: 'atom-region',
        detail: `atom '${id}' region '${node.region}' lies outside matrix ancestry rooted at '${matrixRoot}'`,
      })
    }
    const binder = diagram.regions[node.binder]
    if (
      binder !== undefined
      && binder.kind === 'bubble'
      && diagram.regions[node.region] !== undefined
      && (!prefixSet.has(node.binder) || !ancestryIncludes(diagram, node.binder, node.region))
    ) {
      violations.push({
        code: 'atom-binder',
        detail: `atom '${id}' binder '${node.binder}' must be an enclosing member of the global prefix`,
      })
    }
  }
  if (Object.keys(diagram.wires).length > 0) {
    violations.push({
      code: 'individual-wire',
      detail: 'the Seyric propositional layer cannot contain individual wires',
    })
  }

  return {
    ok: violations.length === 0,
    goalCut,
    prefix,
    matrixRoot,
    violations,
  }
}

const isQuantifierOperation = (step: GameStep): boolean =>
  step.rule === 'comprehensionInstantiate'
  || step.rule === 'comprehensionAbstract'
  || step.rule === 'vacuousIntro'
  || step.rule === 'vacuousElim'

/**
 * Verify that a Seyric authored witness postpones all binder work until the
 * solved matrix is cleaned up, then dissolves the global prefix deepest-first
 * in one uninterrupted block. Only ordinary double-cut cleanup may follow.
 */
export function auditSeyricWitness(
  diagram: Diagram,
  steps: readonly GameStep[],
): SeyricWitnessAudit {
  const start = analyzeSeyricStart(diagram)
  if (!start.ok || start.goalCut === null) {
    return {
      ok: false,
      violations: [{
        code: 'invalid-start',
        detail: 'the witness cannot satisfy Seyric cleanup because its authored start violates Seyric grammar',
      }],
    }
  }

  const violations: SeyricWitnessViolation[] = []
  const expectedBubbles = [...start.prefix].reverse()
  const quantifierSteps = steps
    .map((step, index) => ({ step, index }))
    .filter(({ step }) => isQuantifierOperation(step))
  const firstCleanup = quantifierSteps[0]?.index
  const cleanupBlock = firstCleanup === undefined
    ? []
    : steps.slice(firstCleanup, firstCleanup + expectedBubbles.length)
  const exactPrefix = quantifierSteps.length === expectedBubbles.length
    && cleanupBlock.length === expectedBubbles.length
    && cleanupBlock.every((step, index) =>
      step.rule === 'vacuousElim' && step.region === expectedBubbles[index])
  if (!exactPrefix) {
    violations.push({
      code: 'terminal-cleanup',
      detail: `terminal quantifier cleanup must dissolve exactly ${expectedBubbles.join(', ') || 'no binders'} deepest-first`,
    })
  }

  if (firstCleanup !== undefined) {
    const afterBlock = steps.slice(firstCleanup + expectedBubbles.length)
    if (afterBlock.some((step) => step.rule !== 'doubleCutElim')) {
      violations.push({
        code: 'nonterminal-quantifier-operation',
        detail: 'after the contiguous prefix cleanup block, only ordinary double-cut elimination may remain',
      })
    }
  }

  return { ok: violations.length === 0, violations }
}

export type SeyricPropositionalShape = {
  /** Matrix structure with global proposition names minimized over prefix order. */
  readonly quantifierOrderFingerprint: string
  /** Whether direct matrix siblings exactly match a direct cut's complete contents. */
  readonly immediateComplement: boolean
}

const permutations = function* <T>(values: readonly T[]): Generator<readonly T[]> {
  if (values.length <= 1) {
    yield [...values]
    return
  }
  for (let index = 0; index < values.length; index += 1) {
    const head = values[index]!
    const rest = [...values.slice(0, index), ...values.slice(index + 1)]
    for (const tail of permutations(rest)) yield [head, ...tail]
  }
}

const matrixStructure = (
  diagram: Diagram,
  region: RegionId,
  binderLabels: ReadonlyMap<RegionId, number>,
): string => {
  const members: string[] = []
  for (const node of Object.values(diagram.nodes)) {
    if (node.region !== region) continue
    if (node.kind !== 'atom') throw new Error('Seyric matrix structure requires atom-only content')
    const label = binderLabels.get(node.binder)
    if (label === undefined) throw new Error(`Seyric atom names non-prefix binder '${node.binder}'`)
    members.push(`a${label}`)
  }
  for (const child of directRegions(diagram, region)) {
    const value = diagram.regions[child]!
    if (value.kind !== 'cut') throw new Error('Seyric matrix structure cannot contain a bubble')
    members.push(`c(${matrixStructure(diagram, child, binderLabels)})`)
  }
  members.sort()
  return `r(${members.join(',')})`
}

type DirectItem =
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'node'; readonly id: NodeId }

type ExtractedForm = {
  readonly form: string
  readonly binderAttachments: readonly RegionId[]
}

const directItems = (diagram: Diagram, region: RegionId): readonly DirectItem[] => [
  ...directRegions(diagram, region).map((id): DirectItem => ({ kind: 'region', id })),
  ...directNodes(diagram, region).map((id): DirectItem => ({ kind: 'node', id })),
]

const selectionOf = (
  region: RegionId,
  items: readonly DirectItem[],
): SubgraphSelection => ({
  region,
  regions: items.flatMap((item) => item.kind === 'region' ? [item.id] : []),
  nodes: items.flatMap((item) => item.kind === 'node' ? [item.id] : []),
  wires: [],
})

const extractedForm = (
  diagram: Diagram,
  selection: SubgraphSelection,
): ExtractedForm | null => {
  try {
    const extracted = extractSubgraph(diagram, selection)
    return {
      form: boundaryForm(extracted.pattern),
      binderAttachments: extracted.binderAttachments,
    }
  } catch (error) {
    if (error instanceof DiagramError) return null
    throw error
  }
}

const sameExtractedForm = (left: ExtractedForm, right: ExtractedForm): boolean =>
  left.form === right.form
  && left.binderAttachments.length === right.binderAttachments.length
  && left.binderAttachments.every((binder, index) => binder === right.binderAttachments[index])

const nonemptySubsets = function* <T>(values: readonly T[]): Generator<readonly T[]> {
  const selected: T[] = []
  const visit = function* (index: number): Generator<readonly T[]> {
    if (index === values.length) {
      if (selected.length > 0) yield [...selected]
      return
    }
    yield* visit(index + 1)
    selected.push(values[index]!)
    yield* visit(index + 1)
    selected.pop()
  }
  yield* visit(0)
}

const exposesImmediateComplement = (diagram: Diagram, matrix: RegionId): boolean => {
  const matrixItems = directItems(diagram, matrix)
  for (const candidateCut of matrixItems) {
    if (
      candidateCut.kind !== 'region'
      || diagram.regions[candidateCut.id]?.kind !== 'cut'
    ) continue

    const cutContents = directItems(diagram, candidateCut.id)
    if (cutContents.length === 0) continue
    const deniedForm = extractedForm(diagram, selectionOf(candidateCut.id, cutContents))
    if (deniedForm === null) continue

    const siblings = matrixItems.filter((item) =>
      item.kind !== 'region' || item.id !== candidateCut.id)
    for (const subset of nonemptySubsets(siblings)) {
      const siblingForm = extractedForm(diagram, selectionOf(matrix, subset))
      if (siblingForm !== null && sameExtractedForm(siblingForm, deniedForm)) return true
    }
  }
  return false
}

/**
 * Analyze only already-valid Seyric authored starts. The order fingerprint
 * preserves every cut boundary while ignoring alpha names and the order of
 * the harmless global proposition prefix. Immediate-complement recognition is
 * a separate exact-occurrence audit and deliberately does not affect that fingerprint.
 */
export function analyzeSeyricPropositionalShape(diagram: Diagram): SeyricPropositionalShape {
  const start = analyzeSeyricStart(diagram)
  if (!start.ok || start.matrixRoot === null) {
    throw new Error('cannot analyze propositional shape of an invalid Seyric start')
  }

  const labels = start.prefix.map((_, index) => index)
  let quantifierOrderFingerprint: string | undefined
  for (const order of permutations(labels)) {
    const binderLabels = new Map(start.prefix.map((binder, index) => [binder, order[index]!] as const))
    const candidate = matrixStructure(diagram, start.matrixRoot, binderLabels)
    if (quantifierOrderFingerprint === undefined || candidate < quantifierOrderFingerprint) {
      quantifierOrderFingerprint = candidate
    }
  }

  const defaultBinderLabels = new Map(
    start.prefix.map((binder, index) => [binder, index] as const),
  )
  return {
    quantifierOrderFingerprint: quantifierOrderFingerprint ?? matrixStructure(
      diagram,
      start.matrixRoot,
      defaultBinderLabels,
    ),
    immediateComplement: exposesImmediateComplement(diagram, start.matrixRoot),
  }
}
