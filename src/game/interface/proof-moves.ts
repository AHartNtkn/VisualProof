import { DiagramBuilder } from '../../kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import { isAncestorOrEqual, polarity } from '../../kernel/diagram/regions'
import { findOccurrences } from '../../kernel/diagram/subgraph/match'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import { mkSelection } from '../../kernel/diagram/subgraph/selection'
import type { ProofContext, ProofStep } from '../../kernel/proof/step'
import { parseTerm } from '../../kernel/term/parse'
import { applyConversion } from '../../kernel/rules/conversion'
import { headNormalize, weakHeadNormalize } from '../../kernel/term/hnf'
import { termNodeAt } from '../../kernel/rules/access'
import { applyConversionByCertificate } from '../../kernel/rules/conversion'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { absorbHits, orphanedWires } from './loupe/edit'
import { buildSelection, type Hit } from './loupe/hittest'
import type { KeySample, PointerClaim, PointerSample } from './loupe/interact/viewport'
import './proof-surface.css'

export type GameProofAction =
  | { readonly kind: 'erase'; readonly label: string }
  | { readonly kind: 'insert'; readonly label: string }
  | { readonly kind: 'doubleCutWrap'; readonly label: string }
  | { readonly kind: 'doubleCutElim'; readonly label: string }
  | { readonly kind: 'vacuousWrap'; readonly label: string }
  | { readonly kind: 'vacuousElim'; readonly label: string }
  | { readonly kind: 'iterate'; readonly label: string }
  | { readonly kind: 'deiterate'; readonly label: string }
  | { readonly kind: 'instantiate'; readonly label: string }
  | { readonly kind: 'convert'; readonly label: string }
  | { readonly kind: 'relUnfold'; readonly label: string }
  | { readonly kind: 'relFold'; readonly label: string }

export type GameProofActionInput =
  | { readonly kind: 'term'; readonly source: string }
  | { readonly kind: 'arity'; readonly arity: number }
  | { readonly kind: 'target'; readonly region: RegionId }
  | { readonly kind: 'conversion'; readonly source: string }
  | { readonly kind: 'construction' }
  | { readonly kind: 'relation'; readonly name: string }

/** Read-only affordance discovery. Kernel appliers remain commit authority. */
export function gameProofActions(
  diagram: Diagram,
  selection: SubgraphSelection,
  context: ProofContext,
  backward = true,
): GameProofAction[] {
  const actions: GameProofAction[] = []
  const sign = polarity(diagram, selection.region)
  const eraseSign = backward ? 'negative' : 'positive'
  const hasContent = selection.nodes.length + selection.regions.length + selection.wires.length > 0
  if (hasContent && sign === eraseSign) actions.push({ kind: 'erase', label: `Erase (${eraseSign} region)` })
  if (!hasContent && sign !== eraseSign) actions.push({ kind: 'insert', label: 'Insert…' })
  actions.push({ kind: 'doubleCutWrap', label: 'Wrap in a double cut' })
  actions.push({ kind: 'vacuousWrap', label: 'Wrap in a vacuous bubble…' })
  if (hasContent) {
    actions.push({ kind: 'iterate', label: 'Iterate by dragging the selection' })
    actions.push({ kind: 'deiterate', label: 'Deiterate (needs a justifying copy)' })
  }
  if (selection.nodes.length === 1 && selection.regions.length === 0
    && diagram.nodes[selection.nodes[0]!]?.kind === 'term') {
    actions.push({ kind: 'convert', label: 'Convert (βη)…' })
  }
  if (selection.nodes.length === 1 && selection.regions.length === 0 && selection.wires.length === 0) {
    const node = diagram.nodes[selection.nodes[0]!]
    if (node?.kind === 'ref' && context.relations.has(node.defId)) {
      actions.push({ kind: 'relUnfold', label: `Unfold ${node.defId}` })
    }
  }
  if (hasContent && context.relations.size > 0) actions.push({ kind: 'relFold', label: 'Fold into a relation…' })
  if (selection.regions.length === 1 && selection.nodes.length === 0 && selection.wires.length === 0) {
    const id = selection.regions[0]!
    const region = diagram.regions[id]!
    if (region.kind === 'cut') {
      const children = Object.values(diagram.regions).filter((candidate) =>
        candidate.kind !== 'sheet' && candidate.parent === id)
      const occupied = Object.values(diagram.nodes).some((node) => node.region === id)
        || Object.values(diagram.wires).some((wire) => wire.scope === id)
      if (children.length === 1 && children[0]?.kind === 'cut' && !occupied) {
        actions.push({ kind: 'doubleCutElim', label: 'Eliminate the double cut' })
      }
    }
    if (region.kind === 'bubble') {
      const bound = Object.values(diagram.nodes).some((node) => node.kind === 'atom' && node.binder === id)
      if (!bound) actions.push({ kind: 'vacuousElim', label: 'Dissolve the vacuous bubble' })
      if (bound && polarity(diagram, id) === (backward ? 'positive' : 'negative')) {
        actions.push({ kind: 'instantiate', label: 'Instantiate the relation…' })
      }
    }
  }
  return actions
}

export function proofShortcutStep(sample: KeySample, selection: readonly Hit[]): ProofStep | null {
  if (sample.repeat || sample.ctrlKey || sample.altKey || sample.metaKey || sample.key.toLowerCase() !== 'f') return null
  return selection.length === 1 && selection[0]?.kind === 'wire'
    ? { rule: 'fusion', wire: selection[0].id }
    : null
}

type Discovery = { readonly selection: SubgraphSelection; readonly actions: readonly GameProofAction[] }

export function discoverGameProofActions(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
): Discovery | null {
  if (hits.length === 0) return null
  try {
    const selection = buildSelection(diagram, absorbHits(diagram, hits))
    return { selection, actions: gameProofActions(diagram, selection, context, true) }
  } catch {
    return null
  }
}

const erasureSelection = (diagram: Diagram, selection: SubgraphSelection): SubgraphSelection => {
  const existing = new Set(selection.wires)
  const riders = orphanedWires(diagram, new Set(selection.nodes))
    .filter((wire) => !existing.has(wire) && diagram.wires[wire]!.scope === selection.region)
  return riders.length === 0 ? selection : { ...selection, wires: [...selection.wires, ...riders] }
}

const deletionStep = (diagram: Diagram, discovery: Discovery, fuel: number): ProofStep | null => {
  const has = (kind: GameProofAction['kind']): boolean => discovery.actions.some((action) => action.kind === kind)
  if (has('doubleCutElim')) return { rule: 'doubleCutElim', region: discovery.selection.regions[0]! }
  if (has('vacuousElim')) return { rule: 'vacuousElim', region: discovery.selection.regions[0]! }
  if (has('erase')) return { rule: 'erasure', sel: erasureSelection(diagram, discovery.selection) }
  if (has('deiterate')) return { rule: 'deiteration', sel: discovery.selection, fuel }
  return null
}

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

const foldedComprehension = (context: ProofContext, name: string): DiagramWithBoundary => {
  const relation = context.relations.get(name)
  if (relation === undefined) throw new Error(`unknown relation '${name}'`)
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, relation.boundary.length)
  const boundary: WireId[] = []
  for (let index = 0; index < relation.boundary.length; index++) {
    boundary.push(builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index } }]))
  }
  return mkDiagramWithBoundary(builder.build(), boundary)
}

const inferFoldArgs = (
  diagram: Diagram,
  selection: SubgraphSelection,
  name: string,
  context: ProofContext,
): WireId[] => {
  const body = context.relations.get(name)
  if (body === undefined) throw new Error(`unknown relation '${name}'`)
  const coveredNodes = new Set(selection.nodes)
  const coveredRegions = new Set<RegionId>()
  const walk = (region: RegionId): void => {
    coveredRegions.add(region)
    for (const [id, child] of Object.entries(diagram.regions)) {
      if (child.kind !== 'sheet' && child.parent === region) walk(id)
    }
  }
  for (const region of selection.regions) walk(region)
  for (const [id, node] of Object.entries(diagram.nodes)) if (coveredRegions.has(node.region)) coveredNodes.add(id)
  for (const occurrence of findOccurrences(diagram, body, {
    fuel: 64,
    inRegion: selection.region,
    mode: 'exact',
  }).matches) {
    const mapped = new Set(occurrence.nodeMap.values())
    if (mapped.size === coveredNodes.size && [...coveredNodes].every((node) => mapped.has(node))) {
      return [...occurrence.attachments]
    }
  }
  throw new Error(`the selection is not an exact occurrence of '${name}'`)
}

const normalizeStep = (diagram: Diagram, node: NodeId, fuel: number, weak: boolean): ProofStep => {
  const result = weak ? weakHeadNormalize(termNodeAt(diagram, node).term, fuel) : headNormalize(termNodeAt(diagram, node).term, fuel)
  if (result.steps.length === 0) throw new Error(`the term is already in ${weak ? 'weak ' : ''}head-normal form`)
  const certificate = { leftSteps: result.steps, rightSteps: [] }
  const step: ProofStep = { rule: 'conversion', node, term: result.term, certificate, attachments: {} }
  applyConversionByCertificate(diagram, node, result.term, certificate, {})
  return step
}

export type GameProofMoveOptions = {
  readonly host: HTMLElement
  readonly active: () => boolean
  readonly diagram: () => Diagram
  readonly engine: () => Engine
  readonly selection: () => readonly Hit[]
  readonly setSelection: (selection: readonly Hit[]) => void
  readonly context: () => ProofContext
  readonly apply: (step: ProofStep) => void
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
  #menu: HTMLDivElement | null = null
  #prompt: HTMLDivElement | null = null
  #drag: IterationDrag | null = null
  #lastPointer: Vec2 = { x: 0, y: 0 }

  constructor(options: GameProofMoveOptions) {
    this.#options = options
    this.#document = options.host.ownerDocument
  }

  claim(sample: PointerSample): PointerClaim | null {
    this.#lastPointer = sample.client
    if (!this.#options.active() || sample.button !== 0) return null
    if (this.#menu !== null) this.#closeMenu()
    if (sample.shiftKey || sample.ctrlKey) return null
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
      this.#openMenu(sample, selection)
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), sample.client)
    }
    return true
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
      const step = deletionStep(this.#options.diagram(), discovery, this.#options.fuel())
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
    action: GameProofAction,
    selection: SubgraphSelection,
    input?: GameProofActionInput,
  ): boolean {
    switch (action.kind) {
      case 'erase':
        this.#commit({ rule: 'erasure', sel: erasureSelection(this.#options.diagram(), selection) })
        return true
      case 'insert':
        if (input?.kind !== 'term') { this.#openTermInsertion(selection.region); return true }
        this.#commit(this.#termInsertionStep(selection.region, input.source))
        return true
      case 'doubleCutWrap':
        this.#commit({ rule: 'doubleCutIntro', sel: selection })
        return true
      case 'doubleCutElim':
        this.#commit({ rule: 'doubleCutElim', region: selection.regions[0]! })
        return true
      case 'vacuousWrap':
        if (input?.kind !== 'arity') { this.#openArityPrompt(selection); return true }
        if (!Number.isInteger(input.arity) || input.arity < 0) throw new Error(`'${input.arity}' is not a valid arity`)
        this.#commit({ rule: 'vacuousIntro', sel: selection, arity: input.arity })
        return true
      case 'vacuousElim':
        this.#commit({ rule: 'vacuousElim', region: selection.regions[0]! })
        return true
      case 'iterate':
        if (input?.kind !== 'target') return false
        this.#commit({ rule: 'iteration', sel: selection, target: input.region })
        return true
      case 'deiterate':
        this.#commit({ rule: 'deiteration', sel: selection, fuel: this.#options.fuel() })
        return true
      case 'convert': {
        if (input?.kind !== 'conversion') return false
        const node = selection.nodes[0]!
        const term = parseTerm(input.source)
        const conversion = applyConversion(this.#options.diagram(), node, term, this.#options.fuel())
        this.#commit({ rule: 'conversion', node, term, certificate: conversion.certificate, attachments: {} })
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
          comp: foldedComprehension(this.#options.context(), input.name), attachments: [], binders: {},
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
    }
  }

  overlay(): readonly Shape[] {
    const drag = this.#drag
    if (drag === null || !drag.moved) return []
    const color = this.#options.theme().interaction.valid
    return drag.targets.flatMap((region) => {
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
    })
  }

  cancel(): void {
    this.#closeMenu()
    this.#closePrompt()
    this.#drag = null
  }

  dispose(): void { this.cancel() }

  #commit(step: ProofStep): void {
    try {
      this.#options.apply(step)
      this.#options.setSelection([])
      this.#closeMenu()
      this.#closePrompt()
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer)
    }
  }

  #openMenu(sample: PointerSample, hits: readonly Hit[]): void {
    const menu = this.#document.createElement('div')
    menu.className = 'curse-proof-menu'
    menu.setAttribute('role', 'menu')
    menu.style.setProperty('--curse-proof-menu-left', `${sample.client.x + 10}px`)
    menu.style.setProperty('--curse-proof-menu-top', `${sample.client.y + 10}px`)
    const row = (label: string, run: (() => void) | null): void => {
      const element = this.#document.createElement(run === null ? 'div' : 'button')
      element.textContent = label
      element.className = run === null ? 'curse-proof-menu__heading' : 'curse-proof-menu__action'
      if (run !== null) element.addEventListener('click', () => {
        try { run() }
        catch (error) {
          this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer)
        }
      })
      menu.append(element)
    }
    const diagram = this.#options.diagram()
    const discovery = hits.length === 0
      ? (() => {
          const selection = mkSelection(diagram, {
            region: regionAt(this.#options.engine(), diagram, sample.world),
            regions: [], nodes: [], wires: [],
          })
          return { selection, actions: gameProofActions(diagram, selection, this.#options.context(), true) }
        })()
      : discoverGameProofActions(diagram, hits, this.#options.context())
    if (discovery === null) return
    row('Seal operations', null)
    for (const action of discovery.actions) this.#appendAction(row, action, discovery.selection)
    if (menu.childElementCount <= 1) return
    this.#menu = menu
    this.#options.host.append(menu)
  }

  #appendAction(
    row: (label: string, run: (() => void) | null) => void,
    action: GameProofAction,
    selection: SubgraphSelection,
  ): void {
    switch (action.kind) {
      case 'erase':
      case 'insert':
      case 'doubleCutWrap':
      case 'doubleCutElim':
      case 'vacuousWrap':
      case 'vacuousElim':
      case 'deiterate':
      case 'relUnfold': row(action.label, () => { this.invokeAction(action, selection) }); return
      case 'iterate': row(action.label, null); return
      case 'convert': this.#appendConversions(row, selection.nodes[0]!); return
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
      }
    }
  }

  #appendConversions(row: (label: string, run: (() => void) | null) => void, node: NodeId): void {
    row('Normalize (also: double-click)', () => this.#commit(normalizeStep(this.#options.diagram(), node, this.#options.fuel(), false)))
    row('Convert to custom target…', () => this.#openTextPrompt('Conversion target', (value) => {
      const term = parseTerm(value)
      const conversion = applyConversion(this.#options.diagram(), node, term, this.#options.fuel())
      this.#commit({ rule: 'conversion', node, term, certificate: conversion.certificate, attachments: {} })
    }))
  }

  #openTermInsertion(region: RegionId): void {
    this.#openTextPrompt('Insertion term', (value) => {
      this.#commit(this.#termInsertionStep(region, value))
    })
  }

  #termInsertionStep(region: RegionId, source: string): ProofStep {
    const builder = new DiagramBuilder()
    builder.termNode(builder.root, parseTerm(source))
    return {
      rule: 'insertion', region,
      pattern: mkDiagramWithBoundary(builder.build(), []), attachments: [], binders: {},
    }
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
