import { portKey, type Diagram, type NodeId, type RegionId, type WireId } from '../../kernel/diagram/diagram'
import { isAncestorOrEqual, polarity } from '../../kernel/diagram/regions'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import { mkSelection } from '../../kernel/diagram/subgraph/selection'
import { applyStep, type ProofStep } from '../../kernel/proof/step'
import type { ProofContext } from '../../kernel/proof/context'
import { singleStepAction, type ProofAction } from '../../kernel/proof/action'
import { parseTerm } from '../../kernel/term/parse'
import { freePorts } from '../../kernel/term/term'
import { applyConversion } from '../../kernel/rules/conversion'
import { proposePortCorrespondence } from '../../kernel/rules/port-correspondence'
import { findInconsistentCutEvidence } from '../../kernel/rules/inconsistent-cut'
import { RuleError } from '../../kernel/rules/error'
import { headNormalize, weakHeadNormalize } from '../../kernel/term/hnf'
import { termNodeAt, wireAt } from '../../kernel/rules/access'
import { applyConversionByCertificate } from '../../kernel/rules/conversion'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { absorbHits } from './loupe/edit'
import { buildSelection, type Hit } from '../../interaction/hittest'
import type { KeySample, PointerClaim, PointerSample } from '../../interaction/controllers/viewport'
import { applicableActions, type ActionDescriptor } from '../../interaction/actions'
import { inferFoldArgs } from '../../interaction/define'
import { ConnectionDragController } from '../../interaction/controllers/connection'
import { FissionDragController } from '../../interaction/controllers/fission'
import {
  proofConnectionStep,
  proposeAttachedPortCorrespondence,
} from '../../interaction/proof-connection'
import {
  contextualDeletionStep,
  deiterationStep,
  erasureStep,
  foldedComprehension,
} from '../../interaction/proof-authoring'
import './context-menu.css'
import './proof-surface.css'

export type GameProofActionInput =
  | { readonly kind: 'target'; readonly region: RegionId }
  | { readonly kind: 'conversion'; readonly source: string }
  | { readonly kind: 'construction' }
  | { readonly kind: 'relation'; readonly name: string }

type ActionSteps = readonly [ProofStep, ...ProofStep[]]

export function proofShortcutStep(sample: KeySample, selection: readonly Hit[]): ProofStep | null {
  if (sample.repeat || sample.ctrlKey || sample.altKey || sample.metaKey || sample.key.toLowerCase() !== 'f') return null
  return selection.length === 1 && selection[0]?.kind === 'wire'
    ? { rule: 'fusion', wire: selection[0].id }
    : null
}

export function selectedHeadStripStep(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
): ProofStep | null {
  const nodes = hits.filter((hit): hit is Extract<Hit, { kind: 'node' }> => hit.kind === 'node')
  const wires = hits.filter((hit): hit is Extract<Hit, { kind: 'wire' }> => hit.kind === 'wire')
  if (nodes.length !== 2 || wires.length > 1 || nodes.length + wires.length !== hits.length) return null
  const [a, b] = nodes.map((hit) => hit.id)
  if (a === undefined || b === undefined || a === b
    || diagram.nodes[a]?.kind !== 'term' || diagram.nodes[b]?.kind !== 'term') return null
  if (wires.length === 1) {
    const selectedWire = wires[0]!.id
    if (wireAt(diagram, a, { kind: 'output' }) !== selectedWire
      || wireAt(diagram, b, { kind: 'output' }) !== selectedWire) return null
  }
  const step: ProofStep = {
    rule: 'headStrip', a, b,
    correspondence: proposeAttachedPortCorrespondence(diagram, a, b),
  }
  try {
    applyStep(diagram, step, context, 'backward')
    return step
  } catch {
    return null
  }
}

type Discovery = { readonly selection: SubgraphSelection; readonly actions: readonly ActionDescriptor[] }

export function discoverGameProofActions(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
): Discovery | null {
  if (hits.length === 0) return null
  try {
    const selection = buildSelection(diagram, absorbHits(diagram, hits))
    return {
      selection,
      actions: applicableActions(diagram, selection, context, true)
        .filter((action) => action.kind !== 'citeTheorem'),
    }
  } catch {
    return null
  }
}

/**
 * Recognize a selected, gapless parent-child chain of vacuous bubble rims.
 * Each proposed elimination is replayed through the ordinary proof authority
 * before the caller is allowed to prepare the batch.
 */
export function vacuousEliminationChainSteps(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
): ActionSteps | null {
  if (hits.length < 2 || hits.some((hit) => hit.kind !== 'region')) return null
  const selected = hits.map((hit) => hit.id)
  if (new Set(selected).size !== selected.length) return null
  if (selected.some((id) => diagram.regions[id]?.kind !== 'bubble')) return null

  const selectedSet = new Set(selected)
  const roots = selected.filter((id) => {
    const region = diagram.regions[id]!
    return region.kind === 'bubble' && !selectedSet.has(region.parent)
  })
  if (roots.length !== 1) return null

  const outerToInner: RegionId[] = []
  let current = roots[0]!
  while (true) {
    outerToInner.push(current)
    const children = selected.filter((id) => {
      const region = diagram.regions[id]!
      return region.kind === 'bubble' && region.parent === current
    })
    if (children.length === 0) break
    if (children.length !== 1) return null
    current = children[0]!
  }
  if (outerToInner.length !== selected.length) return null

  const [deepest, ...remaining] = outerToInner.reverse()
  if (deepest === undefined) return null
  const steps: ActionSteps = [
    { rule: 'vacuousElim', region: deepest },
    ...remaining.map((region): ProofStep => ({ rule: 'vacuousElim', region })),
  ]
  let preflight = diagram
  try {
    for (const step of steps) preflight = applyStep(preflight, step, context, 'backward')
  } catch {
    return null
  }
  return steps
}

const isVacuousBatchRequest = (diagram: Diagram, hits: readonly Hit[]): boolean =>
  hits.filter((hit) => hit.kind === 'region' && diagram.regions[hit.id]?.kind === 'bubble').length >= 2

const iterationTargets = (diagram: Diagram, selection: SubgraphSelection): readonly RegionId[] => {
  const insideSelection = (region: RegionId): boolean => {
    for (let current = region; ;) {
      if (selection.regions.includes(current)) return true
      const value = diagram.regions[current]!
      if (value.kind === 'sheet') return false
      current = value.parent
    }
  }
  return Object.keys(diagram.regions)
    .filter((region) => isAncestorOrEqual(diagram, selection.region, region) && !insideSelection(region))
}

const regionAt = (engine: Engine, diagram: Diagram, point: Vec2): RegionId => {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
      && (best === null || geometry.radius < best.radius)) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
}

const normalizeStep = (diagram: Diagram, node: NodeId, fuel: number, weak: boolean): ProofStep => {
  const current = termNodeAt(diagram, node)
  const result = weak ? weakHeadNormalize(termNodeAt(diagram, node).term, fuel) : headNormalize(termNodeAt(diagram, node).term, fuel)
  if (result.steps.length === 0) throw new Error(`the term is already in ${weak ? 'weak ' : ''}head-normal form`)
  const certificate = { leftSteps: result.steps, rightSteps: [] }
  const correspondence = proposePortCorrespondence(
    current.term,
    result.term,
    current.freePorts,
    freePorts(result.term),
  )
  const step: ProofStep = {
    rule: 'conversion', node, term: result.term, certificate, correspondence, attachments: {},
  }
  applyConversionByCertificate(diagram, node, result.term, certificate, correspondence, {})
  return step
}

export type GameProofMoveOptions = {
  readonly host: HTMLElement
  readonly active: () => boolean
  readonly diagram: () => Diagram
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly selection: () => readonly Hit[]
  readonly setSelection: (selection: readonly Hit[]) => void
  readonly context: () => ProofContext
  readonly apply: (action: ProofAction) => void
  readonly refuse: (text: string, pointer: Vec2) => void
  readonly theme: () => Theme
  readonly fuel: () => number
  readonly openConstruction: (bubble: RegionId, pointer: Vec2) => void
}

type IterationDrag = {
  readonly selection: SubgraphSelection
  readonly targets: readonly RegionId[]
  over: RegionId | null
  moved: boolean
}

const sameHit = (a: Hit, b: Hit): boolean => a.kind === b.kind && a.id === b.id

export class GameProofMoveController {
  readonly #options: GameProofMoveOptions
  readonly #document: Document
  readonly #connection: ConnectionDragController
  readonly #fission: FissionDragController
  #menu: HTMLDivElement | null = null
  #prompt: HTMLDivElement | null = null
  #drag: IterationDrag | null = null
  #lastPointer: Vec2 = { x: 0, y: 0 }

  constructor(options: GameProofMoveOptions) {
    this.#options = options
    this.#document = options.host.ownerDocument
    this.#connection = new ConnectionDragController({
      active: options.active,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: (source, target, pointer) => {
        try {
          this.#commit(proofConnectionStep(
            options.diagram(), source, target, 'backward', options.fuel(),
          ))
          return true
        } catch (error) {
          options.refuse(error instanceof Error ? error.message : String(error), pointer)
          return false
        }
      },
      refuse: options.refuse,
    })
    this.#fission = new FissionDragController({
      active: options.active,
      diagram: options.diagram,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: ({ node, path, at }) => this.#commitAction({
        label: 'fission',
        steps: [{ rule: 'fission', node, path }],
        placements: [{ introducedNode: 0, x: at.x, y: at.y }],
      }),
      refuse: options.refuse,
    })
  }

  claim(sample: PointerSample): PointerClaim | null {
    this.#lastPointer = sample.client
    if (!this.#options.active() || sample.button !== 0) return null
    if (this.#menu !== null) this.#closeMenu()
    if (sample.shiftKey || sample.ctrlKey) return null
    const connection = this.#connection.claim(sample)
    if (connection !== null) return connection
    const fission = this.#fission.claim(sample)
    if (fission !== null) return fission
    if (sample.hit === null
      || !this.#options.selection().some((hit) => sameHit(hit, sample.hit!))) return null
    const discovery = discoverGameProofActions(
      this.#options.diagram(),
      this.#options.selection(),
      this.#options.context(),
    )
    if (discovery === null || !discovery.actions.some((action) => action.kind === 'iterate')) return null
    const drag: IterationDrag = {
      selection: discovery.selection,
      targets: iterationTargets(this.#options.diagram(), discovery.selection),
      over: null,
      moved: false,
    }
    this.#drag = drag
    return {
      still: 'selection',
      blocksPassiveRelaxation: false,
      move: (next) => {
        drag.moved = true
        const region = regionAt(this.#options.engine(), this.#options.diagram(), next.world)
        drag.over = drag.targets.includes(region) ? region : null
        this.#lastPointer = next.client
      },
      release: (next, moved) => {
        this.#lastPointer = next.client
        this.#drag = null
        if (!moved) return
        if (drag.over === null) this.#options.refuse('release inside a glowing region to iterate', next.client)
        else this.#commit({ rule: 'iteration', sel: drag.selection, target: drag.over })
      },
      cancel: () => { this.#drag = null },
    }
  }

  contextMenu(sample: PointerSample): boolean {
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    this.#closeMenu()
    const selection = this.#options.selection()
    if (selection.length > 0
      && (sample.hit === null || !selection.some((hit) => sameHit(hit, sample.hit!)))) return false
    try {
      return this.#openMenu(sample, selection)
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), sample.client)
      return false
    }
  }

  doubleClick(sample: PointerSample): boolean {
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    if (sample.hit?.kind === 'wire') {
      this.#commit({ rule: 'fusion', wire: sample.hit.id })
      return true
    }
    if (sample.hit?.kind !== 'node' || this.#options.diagram().nodes[sample.hit.id]?.kind !== 'term') return false
    try {
      this.#commit(normalizeStep(this.#options.diagram(), sample.hit.id, this.#options.fuel(), true))
    } catch {
      try {
        this.#commit(normalizeStep(this.#options.diagram(), sample.hit.id, this.#options.fuel(), false))
      } catch {
        this.#options.refuse('already in normal form — use a custom conversion target for another βη-equal shape', sample.client)
      }
    }
    return true
  }

  keyDown(sample: KeySample): boolean {
    if (!this.#options.active() || sample.repeat) return false
    if (sample.key === 'Escape') {
      const active = this.#menu !== null || this.#prompt !== null || this.#drag !== null
      this.cancel()
      return active
    }
    const shortcut = proofShortcutStep(sample, this.#options.selection())
    if (shortcut !== null) {
      this.#commit(shortcut)
      return true
    }
    if (!['Delete', 'Backspace', 'w', 'W'].includes(sample.key)) return false
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      const diagram = this.#options.diagram()
      const selection = this.#options.selection()
      const headStrip = selectedHeadStripStep(diagram, selection, this.#options.context())
      if (headStrip !== null) {
        this.#commit(headStrip)
        return true
      }
      const chain = vacuousEliminationChainSteps(
        diagram,
        selection,
        this.#options.context(),
      )
      if (chain !== null) {
        this.#commitSteps(chain)
        return true
      }
      if (isVacuousBatchRequest(diagram, selection)) {
        this.#options.refuse('select one gapless chain of vacuous bubble rims', this.#lastPointer)
        return true
      }
    }
    const discovery = discoverGameProofActions(
      this.#options.diagram(),
      this.#options.selection(),
      this.#options.context(),
    )
    if (discovery === null) {
      this.#options.refuse(
        this.#options.selection().length === 0 ? 'select something first' : 'this selection spans several regions',
        this.#lastPointer,
      )
      return true
    }
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      let step: ProofStep | null
      try {
        step = contextualDeletionStep(
          this.#options.diagram(), discovery.selection, discovery.actions, this.#options.fuel(),
        )
      } catch (error) {
        this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer)
        return true
      }
      if (step === null) this.#options.refuse('nothing here reads as a deletion', this.#lastPointer)
      else this.#commit(step)
      return true
    }
    if (sample.shiftKey) this.#openArityPrompt(discovery.selection)
    else this.#commit({ rule: 'doubleCutIntro', sel: discovery.selection })
    return true
  }

  /** Shared behavioral dispatcher used by rendered menu routes and focused tests. */
  invokeAction(
    action: ActionDescriptor,
    selection: SubgraphSelection,
    input?: GameProofActionInput,
  ): boolean {
    switch (action.kind) {
      case 'erase':
        this.#commit(erasureStep(this.#options.diagram(), selection))
        return true
      case 'doubleCutWrap':
        this.#commit({ rule: 'doubleCutIntro', sel: selection })
        return true
      case 'doubleCutElim':
        this.#commit({ rule: 'doubleCutElim', region: selection.regions[0]! })
        return true
      case 'vacuousElim':
        this.#commit({ rule: 'vacuousElim', region: selection.regions[0]! })
        return true
      case 'iterate':
        if (input?.kind !== 'target') return false
        this.#commit({ rule: 'iteration', sel: selection, target: input.region })
        return true
      case 'deiterate':
        this.#commit(deiterationStep(this.#options.diagram(), selection, this.#options.fuel()))
        return true
      case 'convert': {
        if (input?.kind !== 'conversion') return false
        const node = selection.nodes[0]!
        const term = parseTerm(input.source)
        const current = termNodeAt(this.#options.diagram(), node)
        const correspondence = proposePortCorrespondence(
          current.term, term, current.freePorts, freePorts(term),
        )
        const conversion = applyConversion(
          this.#options.diagram(), node, term, correspondence, this.#options.fuel(),
        )
        this.#commit({
          rule: 'conversion', node, term,
          certificate: conversion.certificate, correspondence, attachments: {},
        })
        return true
      }
      case 'instantiate': {
        const bubble = selection.regions[0]!
        if (input?.kind === 'construction') {
          this.#options.openConstruction(bubble, this.#lastPointer)
          return true
        }
        if (input?.kind !== 'relation') return false
        this.#commit({
          rule: 'comprehensionInstantiate', bubble,
          comp: foldedComprehension(this.#options.context(), input.name), attachments: [], binders: [],
        })
        return true
      }
      case 'abstractWrap': {
        if (input?.kind !== 'relation') return false
        const comp = this.#options.context().relations.get(input.name)
        if (comp === undefined) throw new Error(`unknown relation '${input.name}'`)
        const args = inferFoldArgs(
          this.#options.diagram(), selection, input.name, this.#options.context(),
        )
        this.#commit({
          rule: 'comprehensionAbstract', wrap: selection, comp,
          occurrences: [{ sel: selection, args }],
        })
        return true
      }
      case 'inconsistentCutElim': {
        const result = findInconsistentCutEvidence(
          this.#options.diagram(), selection.regions[0]!, this.#options.fuel(),
        )
        if (result.status === 'undecided') throw new RuleError('inconsistency is undecided under the current fuel')
        if (result.status === 'absent') throw new RuleError('no inconsistent pair was found in the selected cut')
        this.#commit({
          rule: 'inconsistentCutElim', region: selection.regions[0]!,
          first: result.first, second: result.second, certificate: result.certificate,
        })
        return true
      }
      case 'relUnfold':
        this.#commit({ rule: 'relUnfold', node: selection.nodes[0]! })
        return true
      case 'relFold':
        if (input?.kind !== 'relation') return false
        this.#commit({
          rule: 'relFold', sel: selection, defId: input.name,
          args: inferFoldArgs(this.#options.diagram(), selection, input.name, this.#options.context()),
        })
        return true
      case 'citeTheorem':
        return false
    }
  }

  overlay(): readonly Shape[] {
    const drag = this.#drag
    const shared = [...this.#connection.overlay(), ...this.#fission.overlay()]
    if (drag === null || !drag.moved) return shared
    const color = this.#options.theme().interaction.valid
    return [...shared, ...drag.targets.flatMap((region) => {
      if (this.#options.diagram().regions[region]?.kind === 'sheet') return []
      const geometry = this.#options.engine().regions.get(region)
      return geometry === undefined ? [] : [{
        kind: 'circle' as const,
        center: geometry.center,
        r: geometry.radius,
        fill: region === drag.over ? `${color}22` : `${color}10`,
        stroke: color,
        width: region === drag.over ? 2.4 : 1.4,
        insetColor: null,
        glow: null,
      }]
    })]
  }

  cancel(): void {
    this.#closeMenu()
    this.#closePrompt()
    this.#drag = null
    this.#connection.cancel()
    this.#fission.cancel()
  }

  dispose(): void { this.cancel(); this.#fission.dispose() }

  #commit(step: ProofStep): void {
    this.#commitAction(singleStepAction(step.rule, step))
  }

  #commitPlaced(step: ProofStep, at: Vec2): void {
    this.#commitAction(singleStepAction(step.rule, step, [
      { introducedNode: 0, x: at.x, y: at.y },
    ]))
  }

  #commitSteps(steps: ActionSteps): void {
    this.#commitAction({ label: steps.map(({ rule }) => rule).join(' + '), steps, placements: [] })
  }

  #commitAction(action: ProofAction): void {
    try {
      this.#options.apply(action)
      this.#options.setSelection([])
      this.#closeMenu()
      this.#closePrompt()
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer)
    }
  }

  #openMenu(sample: PointerSample, hits: readonly Hit[]): boolean {
    const menu = this.#document.createElement('div')
    menu.className = 'curse-context-menu curse-context-menu--proof'
    menu.setAttribute('role', 'menu')
    menu.style.setProperty('--curse-context-menu-left', `${sample.client.x + 10}px`)
    menu.style.setProperty('--curse-context-menu-top', `${sample.client.y + 10}px`)
    const row = (label: string, run: (() => void) | null): void => {
      const element = this.#document.createElement(run === null ? 'div' : 'button')
      element.textContent = label
      element.className = run === null ? 'curse-context-menu__heading' : 'curse-context-menu__action'
      if (run !== null) element.addEventListener('click', () => {
        try { run() }
        catch (error) {
          this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer)
        }
      })
      menu.append(element)
    }
    const diagram = this.#options.diagram()
    row('Seal operations', null)
    if (hits.length === 1 && hits[0]?.kind === 'wire') {
      this.#appendWireActions(row, hits[0].id)
      if (menu.childElementCount <= 1) return false
      this.#menu = menu
      this.#options.host.append(menu)
      return true
    }
    const discovery = hits.length === 0
      ? (() => {
          const selection = mkSelection(diagram, {
            region: regionAt(this.#options.engine(), diagram, sample.world),
            regions: [], nodes: [], wires: [],
          })
          return {
            selection,
            actions: applicableActions(diagram, selection, this.#options.context(), true)
              .filter((action) => action.kind !== 'citeTheorem'),
          }
        })()
      : discoverGameProofActions(diagram, hits, this.#options.context())
    if (discovery === null) return false
    if (hits.length === 0) this.#appendSpawnActions(row, discovery.selection.region, sample.world)
    for (const action of discovery.actions) this.#appendAction(row, action, discovery.selection)
    if (menu.childElementCount <= 1) return false
    this.#menu = menu
    this.#options.host.append(menu)
    return true
  }

  #appendAction(
    row: (label: string, run: (() => void) | null) => void,
    action: ActionDescriptor,
    selection: SubgraphSelection,
  ): void {
    switch (action.kind) {
      case 'erase':
      case 'doubleCutWrap':
      case 'doubleCutElim':
      case 'vacuousElim':
      case 'deiterate':
      case 'inconsistentCutElim':
      case 'relUnfold': row(action.label, () => { this.invokeAction(action, selection) }); return
      case 'iterate': row(action.label, null); return
      case 'convert': this.#appendConversions(row, selection.nodes[0]!); return
      case 'abstractWrap': {
        for (const name of this.#options.context().relations.keys()) row(`Abstract as ${name}`, () => {
          this.invokeAction(action, selection, { kind: 'relation', name })
        })
        return
      }
      case 'instantiate': {
        const bubble = selection.regions[0]!
        const value = this.#options.diagram().regions[bubble]!
        const arity = value.kind === 'bubble' ? value.arity : -1
        row('Construct a new relation…', () => {
          this.#closeMenu()
          this.invokeAction(action, selection, { kind: 'construction' })
        })
        for (const [name, relation] of this.#options.context().relations) {
          if (relation.boundary.length === arity) row(`Use ${name}`, () => {
            this.invokeAction(action, selection, { kind: 'relation', name })
          })
        }
        return
      }
      case 'relFold': {
        for (const name of this.#options.context().relations.keys()) row(`Fold into ${name}`, () => {
          this.invokeAction(action, selection, { kind: 'relation', name })
        })
        return
      }
      case 'citeTheorem': return
    }
  }

  #appendSpawnActions(
    row: (label: string, run: (() => void) | null) => void,
    region: RegionId,
    at: Vec2,
  ): void {
    if (polarity(this.#options.diagram(), region) !== 'positive') return
    row('Spawn', null)
    row('Term…', () => this.#openTermSpawn(region, at))
    for (const [name, relation] of this.#options.context().relations) {
      row(`Relation ${name}`, () => this.#commitPlaced({
        rule: 'relationSpawn', region, defId: name, arity: relation.boundary.length,
      }, at))
    }
    for (const [binder, value] of Object.entries(this.#options.diagram().regions)) {
      if (value.kind !== 'bubble' || !isAncestorOrEqual(this.#options.diagram(), binder, region)) continue
      row(`Bound predicate ${binder}`, () => this.#commitPlaced({
        rule: 'boundRelationSpawn', region, binder, arity: value.arity,
      }, at))
    }
  }

  #appendWireActions(row: (label: string, run: (() => void) | null) => void, wireId: WireId): void {
    const diagram = this.#options.diagram()
    const wire = diagram.wires[wireId]
    if (wire === undefined) return
    row('Line operations', null)
    wire.endpoints.slice(0, -1).forEach((endpoint, index) => {
      const step: ProofStep = {
        rule: 'wireSever', wire: wireId, keep: wire.endpoints.slice(0, index + 1),
      }
      try { applyStep(diagram, step, this.#options.context(), 'backward') }
      catch { return }
      row(`Sever after ${endpoint.node}/${portKey(endpoint.port)}`, () => this.#commit(step))
    })
    const witnesses = wire.endpoints.filter((endpoint) => {
      const node = diagram.nodes[endpoint.node]
      return endpoint.port.kind === 'output' && node?.kind === 'term' && node.freePorts.length === 0
    })
    for (const witness of witnesses) for (const endpoint of wire.endpoints) {
      if (endpoint.node === witness.node && portKey(endpoint.port) === portKey(witness.port)) continue
      const step: ProofStep = {
        rule: 'anchoredWireSplit', wire: wireId, witness: witness.node,
        endpoints: [endpoint], target: diagram.nodes[endpoint.node]!.region,
      }
      try { applyStep(diagram, step, this.#options.context(), 'backward') }
      catch { continue }
      row(`Split ${endpoint.node}/${portKey(endpoint.port)} from ${witness.node}`, () => this.#commit(step))
    }
  }

  #appendConversions(row: (label: string, run: (() => void) | null) => void, node: NodeId): void {
    row('Normalize (also: double-click)', () => this.#commit(normalizeStep(this.#options.diagram(), node, this.#options.fuel(), false)))
    row('Convert to custom target…', () => this.#openTextPrompt('Conversion target', (value) => {
      const term = parseTerm(value)
      const current = termNodeAt(this.#options.diagram(), node)
      const correspondence = proposePortCorrespondence(
        current.term, term, current.freePorts, freePorts(term),
      )
      const conversion = applyConversion(
        this.#options.diagram(), node, term, correspondence, this.#options.fuel(),
      )
      this.#commit({
        rule: 'conversion', node, term,
        certificate: conversion.certificate, correspondence, attachments: {},
      })
    }))
  }

  #openTermSpawn(region: RegionId, at: Vec2): void {
    this.#openTextPrompt('Spawn term', (value) => {
      this.#commitPlaced(this.#termSpawnStep(region, value), at)
    })
  }

  #termSpawnStep(region: RegionId, source: string): ProofStep {
    const term = parseTerm(source)
    const declared = freePorts(term)
    return declared.length === 0
      ? { rule: 'closedTermIntro', region, term }
      : { rule: 'openTermSpawn', region, term, freePorts: declared }
  }

  #openArityPrompt(selection: SubgraphSelection): void {
    this.#openTextPrompt('Bubble arity', (value) => {
      const arity = Number(value)
      if (!Number.isInteger(arity) || arity < 0) throw new Error(`'${value}' is not a valid arity`)
      this.#commit({ rule: 'vacuousIntro', sel: selection, arity })
    })
  }

  #openTextPrompt(label: string, submit: (value: string) => void): void {
    this.#closePrompt()
    const prompt = this.#document.createElement('div')
    prompt.className = 'curse-proof-prompt'
    const input = this.#document.createElement('input')
    input.setAttribute('aria-label', label)
    const button = this.#document.createElement('button')
    button.textContent = 'Apply'
    const run = (): void => {
      try { submit(input.value) }
      catch (error) { this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer) }
    }
    button.addEventListener('click', run)
    input.addEventListener('keydown', (event) => {
      if (event.key === 'Enter') {
        event.preventDefault()
        event.stopPropagation()
        run()
      } else if (event.key === 'Escape') {
        event.preventDefault()
        event.stopPropagation()
        this.#closePrompt()
      }
    })
    prompt.append(input, button)
    this.#prompt = prompt
    this.#options.host.append(prompt)
    input.focus()
  }

  #closeMenu(): void { this.#menu?.remove(); this.#menu = null }
  #closePrompt(): void { this.#prompt?.remove(); this.#prompt = null }
}
