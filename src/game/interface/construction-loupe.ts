import type { Diagram, NodeId, RegionId, WireId } from '../../kernel/diagram/diagram'
import { parseTerm } from '../../kernel/term/parse'
import type { ProofStep } from '../../kernel/proof/step'
import type { ProofContext } from '../../kernel/proof/context'
import { carryOver, mkEngine, resolvedFrameSlot, type Engine } from '../../view/engine'
import { bubbleHues, paint, type Shape, type Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { adaptCanvas, type CanvasAdapter } from '../../view/canvas'
import { seedProject } from '../../view/relax'
import { existentialStubs, legPaths } from '../../view/wires'
import { addAtomNode, addRefNode, addTermNode } from './loupe/edit'
import { wireHitTest, type Hit } from './loupe/hittest'
import { ConstructController } from './loupe/interact/construct'
import { SpawnCascade, boundPredicateOptions } from './loupe/interact/spawn'
import { InteractiveViewport, type KeySample, type MutableView, type PointerClaim, type PointerSample } from './loupe/interact/viewport'
import {
  applyComprehensionConnection,
  currentComprehensionDraft,
  materializeComprehensionSnapshot,
  moveComprehensionHistory,
  planComprehensionConnection,
  replaceComprehensionDiagram,
  beginComprehensionDraft,
  deriveExternalReferencePresentation,
  type ComprehensionConnectionEndpoint,
  type ComprehensionDraft,
  type ExternalWireBinding,
} from './loupe/draft'
import {
  beginLoupeResize,
  clientToLoupeDraft,
  hitConstructionLoupe,
  loupeApertureRect,
  loupeRimHitWidth,
  moveConstructionLoupe,
  placeConstructionLoupe,
  resizeConstructionLoupe,
  type LoupeGeometry,
} from './construction-loupe-geometry'
import './construction-loupe.css'

export type ConstructionLoupeKeyAction = 'commit' | 'close' | 'undo' | 'redo'

export function resolveConstructionLoupeKey(sample: KeySample, editingText: boolean): ConstructionLoupeKeyAction | null {
  if (sample.repeat) return null
  const key = sample.key.toLowerCase()
  if ((sample.ctrlKey || sample.metaKey) && key === 'z') return sample.shiftKey ? 'redo' : 'undo'
  if (sample.key === 'Enter') return 'commit'
  if (sample.key === 'Escape') return 'close'
  if (sample.key === 'Backspace' && !editingText) return 'close'
  return null
}

export function isConstructionTextEntry(target: EventTarget | null): boolean {
  if (target === null || typeof target !== 'object' || !('nodeType' in target)) return false
  const element = target as HTMLElement
  return element.isContentEditable || element.tagName === 'INPUT' || element.tagName === 'TEXTAREA'
}

export const CONSTRUCTION_LOUPE_ASSETS = Object.freeze({
  rim: new URL('../../../assets/interface/generated/editor-loupe/rim-socket.png', import.meta.url).href,
  handle: new URL('../../../assets/interface/generated/editor-loupe/handle-terminal.png', import.meta.url).href,
  optics: new URL('../../../assets/interface/generated/editor-loupe/optical-edge.png', import.meta.url).href,
})

export function connectionTargets(
  draft: ComprehensionDraft,
  source: ComprehensionConnectionEndpoint,
): { readonly draft: ReadonlySet<WireId>; readonly host: ReadonlySet<WireId> } {
  const draftTargets = new Set<WireId>()
  const hostTargets = new Set<WireId>()
  const current = draft.history[draft.cursor]!
  for (const wire of Object.keys(current.relation.diagram.wires)) {
    if (planComprehensionConnection(draft, source, { kind: 'draft', wire }).ok) draftTargets.add(wire)
  }
  for (const wire of Object.keys(draft.host.wires)) {
    if (planComprehensionConnection(draft, source, { kind: 'host', wire }).ok) hostTargets.add(wire)
  }
  return { draft: draftTargets, host: hostTargets }
}

export function formalBoundaryMarks(boundary: readonly WireId[]): readonly {
  readonly wire: WireId
  readonly position: number
  readonly orientation: boolean
}[] {
  return boundary.map((wire, position) => ({ wire, position, orientation: position === 0 }))
}

export function applyLoupeConnection(
  draft: ComprehensionDraft,
  captured: ComprehensionDraft['history'][number],
  source: ComprehensionConnectionEndpoint,
  target: ComprehensionConnectionEndpoint,
): ComprehensionDraft {
  if (currentComprehensionDraft(draft) !== captured) throw new Error('connection cancelled because the draft changed')
  return applyComprehensionConnection(draft, source, target)
}

export function constructionInstantiationStep(draft: ComprehensionDraft): ProofStep {
  const materialized = materializeComprehensionSnapshot(currentComprehensionDraft(draft))
  return {
    rule: 'comprehensionInstantiate', bubble: draft.bubble,
    comp: materialized.relation,
    attachments: materialized.attachments,
    binders: [],
  }
}

export type ConstructionLoupeHost = {
  readonly mount: HTMLElement
  readonly canvas: HTMLCanvasElement
  diagram(): Diagram
  boundary(): readonly WireId[]
  engine(): Engine
  view(): MutableView
  context(): ProofContext
  orientation(): 'forward' | 'backward'
  theme(): Theme
  apply(step: ProofStep): void
  refuse(text: string, pointer: Vec2): void
  changed(): void
  openChanged(open: boolean): void
  reducedMotion?(): boolean
}

export type ConstructionLoupeDebug = {
  readonly bubble: RegionId
  readonly cursor: number
  readonly historyLength: number
  readonly formalBoundary: readonly WireId[]
  readonly materializedBoundary: readonly WireId[]
  readonly externalWires: readonly ExternalWireBinding[]
  readonly geometry: LoupeGeometry
  readonly lastContextMenuMapping: null | {
    readonly client: Vec2
    readonly screen: Vec2
    readonly world: Vec2
  }
  readonly draftBodies: readonly { readonly node: NodeId; readonly kind: string; readonly x: number; readonly y: number; readonly point: Vec2 }[]
  readonly draftWires: readonly { readonly wire: WireId; readonly point: Vec2 | null }[]
  readonly hostWires: readonly { readonly wire: WireId; readonly point: Vec2 | null }[]
  readonly connection: null | {
    readonly source: ComprehensionConnectionEndpoint
    readonly draftTargets: readonly WireId[]
    readonly hostTargets: readonly WireId[]
  }
}

type SurfaceKind = 'host' | 'draft'
type ConnectionGesture = {
  readonly source: ComprehensionConnectionEndpoint
  readonly captured: ComprehensionDraft['history'][number]
  readonly start: Vec2
  current: Vec2
  moved: boolean
}

const wireShapes = (engine: Engine, wire: WireId, stroke: string, width: number, glow: string | null = null): Shape[] => {
  const shapes: Shape[] = []
  for (const path of legPaths(engine)) if (path.wid === wire) shapes.push({ kind: 'polyline', pts: path.pts, stroke, width, glow })
  for (const stub of existentialStubs(engine)) if (stub.wid === wire) shapes.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width, glow })
  return shapes
}

const itemShapes = (engine: Engine, hit: Hit, stroke: string): Shape[] => {
  if (hit.kind === 'wire') return wireShapes(engine, hit.id, stroke, 3)
  if (hit.kind === 'node') {
    const body = engine.bodies.get(hit.id)
    return body === undefined ? [] : [{ kind: 'circle', center: body.pos, r: body.discR * engine.scale + 1, fill: null, stroke, width: 2, insetColor: null, glow: null }]
  }
  const region = engine.regions.get(hit.id)
  return region === undefined ? [] : [{ kind: 'circle', center: region.center, r: region.radius, fill: null, stroke, width: 2, insetColor: null, glow: null }]
}

export class ConstructionLoupe {
  readonly #host: ConstructionLoupeHost
  readonly #window: Window & typeof globalThis
  readonly #root: HTMLDivElement
  readonly #canvas: HTMLCanvasElement
  readonly #surface: CanvasAdapter
  readonly #view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
  readonly #interaction: InteractiveViewport
  readonly #construct: ConstructController
  readonly #spawn: SpawnCascade
  readonly #gesture: SVGSVGElement
  #draft: ComprehensionDraft
  #engine: Engine
  #geometry: LoupeGeometry
  #connection: ConnectionGesture | null = null
  #draftHoverWire: WireId | null = null
  #hostHoverWire: WireId | null = null
  #lastContextMenuMapping: ConstructionLoupeDebug['lastContextMenuMapping'] = null
  #geometryVersion = 0
  #disposed = false

  constructor(host: ConstructionLoupeHost, bubble: RegionId, invocation: Vec2) {
    this.#host = host
    this.#draft = beginComprehensionDraft(host.diagram(), bubble, host.orientation())
    const materialized = materializeComprehensionSnapshot(currentComprehensionDraft(this.#draft))
    this.#engine = mkEngine(materialized.relation.diagram, materialized.relation.boundary)
    seedProject(this.#engine)
    const viewport = host.mount.ownerDocument.defaultView
    if (viewport === null) throw new Error('construction loupe host must belong to a live window')
    this.#window = viewport
    this.#geometry = placeConstructionLoupe(invocation, {
      width: viewport.innerWidth,
      height: viewport.innerHeight,
    })

    const document = host.mount.ownerDocument
    this.#root = document.createElement('div')
    this.#root.className = 'cursebreaker-construction-loupe'
    this.#root.classList.toggle('is-reduced-motion', host.reducedMotion?.() ?? false)
    this.#root.setAttribute('role', 'dialog')
    this.#root.setAttribute('aria-modal', 'false')
    this.#root.setAttribute('aria-label', `Circular relation construction loupe, arity ${this.#draft.arity}`)
    const instructions = document.createElement('p')
    instructions.className = 'cursebreaker-construction-loupe__instructions'
    instructions.textContent = 'Enter commits. Escape or Backspace closes. Control Z undoes within this construction.'
    this.#canvas = document.createElement('canvas')
    this.#canvas.className = 'cursebreaker-construction-loupe__canvas'
    this.#canvas.setAttribute('aria-label', 'Anonymous circular relation draft')
    this.#canvas.tabIndex = 0
    const rimArtwork = this.#artLayer('rim', CONSTRUCTION_LOUPE_ASSETS.rim)
    const optics = this.#artLayer('optics', CONSTRUCTION_LOUPE_ASSETS.optics)
    const handleArtwork = this.#artLayer('handle', CONSTRUCTION_LOUPE_ASSETS.handle)
    const rim = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
    rim.classList.add('cursebreaker-construction-loupe__rim-hit')
    rim.setAttribute('aria-label', 'Move construction loupe')
    rim.setAttribute('viewBox', '0 0 100 100')
    const definitions = document.createElementNS('http://www.w3.org/2000/svg', 'defs')
    const clip = document.createElementNS('http://www.w3.org/2000/svg', 'clipPath')
    clip.id = 'cursebreaker-construction-loupe-rim-clip'
    clip.setAttribute('clipPathUnits', 'objectBoundingBox')
    const annulus = document.createElementNS('http://www.w3.org/2000/svg', 'path')
    annulus.setAttribute('d', 'M .5 0 A .5 .5 0 1 1 .5 1 A .5 .5 0 1 1 .5 0 Z M .5 .08 A .42 .42 0 1 0 .5 .92 A .42 .42 0 1 0 .5 .08 Z')
    annulus.setAttribute('clip-rule', 'evenodd')
    clip.append(annulus)
    definitions.append(clip)
    rim.setAttribute('clip-path', 'url(#cursebreaker-construction-loupe-rim-clip)')
    const rimStroke = document.createElementNS('http://www.w3.org/2000/svg', 'circle')
    rimStroke.setAttribute('cx', '50')
    rimStroke.setAttribute('cy', '50')
    rimStroke.setAttribute('r', '48')
    rimStroke.classList.add('cursebreaker-construction-loupe__rim-hit-stroke')
    rim.append(definitions, rimStroke)
    const terminal = document.createElement('div')
    terminal.className = 'cursebreaker-construction-loupe__terminal-hit'
    terminal.setAttribute('role', 'separator')
    terminal.setAttribute('aria-label', 'Resize construction loupe proportionally')
    this.#root.append(instructions, this.#canvas, optics, rimArtwork, handleArtwork, rim, terminal)
    this.#gesture = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
    this.#gesture.classList.add('cursebreaker-construction-loupe__gesture')
    host.mount.append(this.#root, this.#gesture)
    this.#applyGeometry()
    this.#surface = adaptCanvas(this.#canvas)

    this.#spawn = new SpawnCascade({
      host: host.mount,
      spawnTerm: ({ source, invocation: at }) => this.#editAdd(() => addTermNode(this.#diagram(), at.region, parseTerm(source)), at.world),
      spawnRelation: ({ defId, arity, invocation: at }) => this.#editAdd(() => addRefNode(this.#diagram(), at.region, defId, arity), at.world),
      spawnBoundPredicate: ({ binder, invocation: at }) => this.#editAdd(() => addAtomNode(this.#diagram(), at.region, binder), at.world),
      binderColor: (binder) => bubbleHues(this.#diagram(), host.theme().bubbleLightness).get(binder) ?? host.theme().interaction.hover,
      openChanged: host.changed,
    })
    this.#construct = new ConstructController({
      host: this.#root,
      active: () => !this.#disposed,
      engine: () => this.#engine,
      viewScale: () => this.#view.scale,
      diagram: () => this.#diagram(),
      selection: () => this.#interaction.selection,
      setSelection: (selection) => this.#interaction.setSelection(selection),
      commit: (diagram) => this.#commitDiagram(diagram),
      refuse: (text, pointer) => host.refuse(text, pointer ?? invocation),
      setProblem: (_id, text) => host.refuse(text, invocation),
      clearProblem: () => {},
      openSpawn: (sample, region) => this.#spawn.open(
        { screen: sample.client, world: sample.world, region },
        host.context().relations,
        boundPredicateOptions(this.#diagram(), region),
      ),
      theme: host.theme,
    })
    this.#interaction = new InteractiveViewport({
      canvas: this.#canvas,
      view: this.#view,
      engine: () => this.#engine,
      diagram: () => this.#diagram(),
      selectionEnabled: () => true,
      claim: (sample) => this.#connectionClaim('draft', sample) ?? this.#construct.claim(sample),
      doubleClick: (sample) => this.#construct.doubleClick(sample),
      contextMenu: (sample) => {
        this.#lastContextMenuMapping = {
          client: { ...sample.client }, screen: { ...sample.screen }, world: { ...sample.world },
        }
        const region = this.#regionAt(sample.world)
        this.#spawn.open({ screen: sample.client, world: sample.world, region }, host.context().relations, boundPredicateOptions(this.#diagram(), region))
      },
      pointerChanged: (client) => this.#pointerChanged('draft', client),
      keyDown: (sample) => this.keyDown(sample, isConstructionTextEntry(document.activeElement)),
      keyScope: 'window',
      selectionChanged: host.changed,
      selectionCommitted: host.changed,
      mapClient: (client) => this.clientMapping(client),
    })

    this.#installMove(this.#root)
    this.#installResize(terminal)
    this.#window.addEventListener('resize', this.#resizeViewport)
    host.openChanged(true)
    host.changed()
    queueMicrotask(() => this.#canvas.focus())
  }

  get active(): boolean { return !this.#disposed }
  get playingGesture(): boolean { return this.#connection?.moved ?? false }

  hostClaim(sample: PointerSample): PointerClaim | null {
    const claim = this.#connectionClaim('host', sample)
    return claim === null ? null : { ...claim, still: 'claim' }
  }

  hostPointerChanged(client: Vec2): void { this.#pointerChanged('host', client) }

  clientMapping(client: Vec2): { readonly screen: Vec2; readonly world: Vec2 } {
    const rect = this.#canvas.getBoundingClientRect()
    return clientToLoupeDraft(client, {
      left: rect.left, top: rect.top, width: rect.width, height: rect.height,
    }, {
      width: this.#canvas.width, height: this.#canvas.height,
    }, this.#view)
  }

  setReducedMotion(enabled: boolean): void {
    this.#root.classList.toggle('is-reduced-motion', enabled)
  }

  keyDown(sample: KeySample, editingText = false): boolean {
    if (this.#disposed || sample.repeat) return false
    if (editingText && (sample.key === 'Backspace' || sample.key === 'Enter')) return false
    const action = resolveConstructionLoupeKey(sample, editingText)
    if (action === 'undo' || action === 'redo') {
      this.#moveHistory(action === 'undo' ? -1 : 1)
      return true
    }
    if (action === 'close') { this.cancel(); return true }
    if (action === 'commit') { this.#instantiate(); return true }
    return this.#construct.keyDown(sample)
  }

  hostOverlays(): readonly Shape[] { return this.#connectionShapes('host') }

  frame(_now: number): void {
    if (this.#disposed || !this.#surface.syncSize()) return
    this.#interaction.advance(this.#connection === null)
    const theme = this.#host.theme()
    const shapes: Shape[] = paint(this.#engine, theme).filter((shape) => shape.kind !== 'frame')
    for (const hit of this.#interaction.selection) shapes.push(...itemShapes(this.#engine, hit, theme.interaction.selection))
    if (this.#interaction.hover !== null) shapes.push(...itemShapes(this.#engine, this.#interaction.hover, theme.interaction.hover))
    for (const id of this.#interaction.pins) {
      const body = this.#engine.bodies.get(id)
      if (body !== undefined) shapes.push({ kind: 'circle', center: body.pos, r: body.discR * this.#engine.scale + 1, fill: null, stroke: theme.interaction.pin, width: 1.5, insetColor: null, glow: null })
    }
    shapes.push(...this.#construct.overlay(), ...this.#connectionShapes('draft'))
    const slot = resolvedFrameSlot(this.#engine, 0)
    if (slot !== null) shapes.push({ kind: 'dot', center: slot.point, rPx: 8, fill: theme.interaction.selection })
    this.#surface.render({ layers: [{ shapes }] }, this.#view)
    this.#renderGesture()
  }

  cancel(): void { this.dispose() }

  debugState(): ConstructionLoupeDebug {
    const current = currentComprehensionDraft(this.#draft)
    const materialized = materializeComprehensionSnapshot(current)
    const source = this.#connection?.source ?? this.#hoverSource()
    const targets = source === null ? null : connectionTargets(this.#draft, source)
    return {
      bubble: this.#draft.bubble,
      cursor: this.#draft.cursor,
      historyLength: this.#draft.history.length,
      formalBoundary: [...current.relation.boundary],
      materializedBoundary: [...materialized.relation.boundary],
      externalWires: [...current.externalWires],
      geometry: { center: { ...this.#geometry.center }, diameter: this.#geometry.diameter },
      lastContextMenuMapping: this.#lastContextMenuMapping === null ? null : {
        client: { ...this.#lastContextMenuMapping.client },
        screen: { ...this.#lastContextMenuMapping.screen },
        world: { ...this.#lastContextMenuMapping.world },
      },
      draftBodies: [...this.#engine.bodies].map(([node, body]) => ({
        node,
        kind: body.kind,
        x: body.pos.x,
        y: body.pos.y,
        point: this.#worldToClient(this.#canvas, this.#view, body.pos),
      })),
      draftWires: Object.keys(current.relation.diagram.wires).map((wire) => ({ wire, point: this.#wireClientPoint('draft', wire) })),
      hostWires: Object.keys(this.#host.diagram().wires).map((wire) => ({ wire, point: this.#wireClientPoint('host', wire) })),
      connection: source === null || targets === null ? null : {
        source, draftTargets: [...targets.draft], hostTargets: [...targets.host],
      },
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.#window.removeEventListener('resize', this.#resizeViewport)
    this.#connection = null
    this.#spawn.dispose()
    this.#construct.dispose()
    this.#interaction.dispose()
    this.#root.remove()
    this.#gesture.remove()
    this.#host.openChanged(false)
    this.#host.changed()
    this.#host.canvas.focus()
  }

  #diagram(): Diagram { return currentComprehensionDraft(this.#draft).relation.diagram }

  #artLayer(kind: 'rim' | 'handle' | 'optics', src: string): HTMLImageElement {
    const image = this.#host.mount.ownerDocument.createElement('img')
    image.className = `cursebreaker-construction-loupe__art cursebreaker-construction-loupe__art--${kind}`
    image.src = src
    image.alt = ''
    image.setAttribute('aria-hidden', 'true')
    image.draggable = false
    return image
  }

  #commitDiagram(diagram: Diagram): void {
    try {
      this.#draft = replaceComprehensionDiagram(this.#draft, diagram)
      this.#reconcile()
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
    }
  }

  #editAdd(change: () => { diagram: Diagram; node: string }, at: Vec2): boolean {
    try {
      const added = change()
      this.#draft = replaceComprehensionDiagram(this.#draft, added.diagram)
      this.#reconcile({ node: added.node, at })
      return true
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
      return false
    }
  }

  #reconcile(placed?: { readonly node: string; readonly at: Vec2 }): void {
    const current = materializeComprehensionSnapshot(currentComprehensionDraft(this.#draft))
    const next = mkEngine(current.relation.diagram, current.relation.boundary)
    carryOver(this.#engine, next)
    if (placed !== undefined) {
      const body = next.bodies.get(placed.node)
      if (body !== undefined) body.pos = { ...placed.at }
    }
    seedProject(next)
    this.#engine = next
    this.#connection = null
    this.#draftHoverWire = null
    this.#hostHoverWire = null
    this.#interaction.reconcileDiagram()
    this.#host.changed()
  }

  #moveHistory(delta: number): void {
    const next = moveComprehensionHistory(this.#draft, delta)
    if (next.cursor === this.#draft.cursor) {
      this.#host.refuse(`nothing to ${delta < 0 ? 'undo' : 'redo'} in the relation draft`, this.#centerClient())
      return
    }
    this.#draft = next
    this.#reconcile()
  }

  #instantiate(): void {
    try {
      this.#host.apply(constructionInstantiationStep(this.#draft))
      this.dispose()
    } catch (error) {
      this.#host.refuse(error instanceof Error ? error.message : String(error), this.#centerClient())
    }
  }

  #connectionClaim(surface: SurfaceKind, sample: PointerSample): PointerClaim | null {
    if (this.#disposed || sample.button !== 0 || sample.ctrlKey || sample.shiftKey) return null
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const view = surface === 'draft' ? this.#view : this.#host.view()
    const wire = wireHitTest(engine, sample.world, { scale: view.scale })?.id
    if (wire === undefined) return null
    const gesture: ConnectionGesture = {
      source: { kind: surface, wire }, captured: currentComprehensionDraft(this.#draft),
      start: sample.client, current: sample.client, moved: false,
    }
    this.#connection = gesture
    return {
      still: 'selection', blocksPassiveRelaxation: true,
      move: (next) => {
        gesture.current = next.client
        gesture.moved ||= Math.hypot(next.client.x - gesture.start.x, next.client.y - gesture.start.y) > 3
        this.#host.changed()
      },
      release: (next, moved) => {
        gesture.current = next.client
        if (!moved || !gesture.moved) { this.#connection = null; return }
        const target = this.#endpointAtClient(next.client)
        this.#connection = null
        if (target === null) {
          this.#host.refuse('release on an eligible line in the draft or proof', next.client)
          return
        }
        try {
          this.#draft = applyLoupeConnection(this.#draft, gesture.captured, gesture.source, target)
          this.#reconcile()
        } catch (error) {
          this.#host.refuse(error instanceof Error ? error.message : String(error), next.client)
        }
      },
      cancel: () => { if (this.#connection === gesture) this.#connection = null },
    }
  }

  #endpointAtClient(client: Vec2): ComprehensionConnectionEndpoint | null {
    const top = this.#host.mount.ownerDocument.elementFromPoint(client.x, client.y)
    if (top !== this.#canvas && top !== this.#host.canvas) return null
    const kind: SurfaceKind = top === this.#canvas ? 'draft' : 'host'
    const canvas = kind === 'draft' ? this.#canvas : this.#host.canvas
    const engine = kind === 'draft' ? this.#engine : this.#host.engine()
    const view = kind === 'draft' ? this.#view : this.#host.view()
    const rect = canvas.getBoundingClientRect()
    const mapping = kind === 'draft'
      ? this.clientMapping(client)
      : clientToLoupeDraft(client, {
        left: rect.left, top: rect.top, width: rect.width, height: rect.height,
      }, { width: canvas.width, height: canvas.height }, view)
    const world = mapping.world
    const wire = wireHitTest(engine, world, { scale: view.scale })?.id
    return wire === undefined ? null : { kind, wire }
  }

  #wireClientPoint(surface: SurfaceKind, wire: WireId): Vec2 | null {
    const canvas = surface === 'draft' ? this.#canvas : this.#host.canvas
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const view = surface === 'draft' ? this.#view : this.#host.view()
    const points: Vec2[] = []
    for (const leg of legPaths(engine)) if (leg.wid === wire) points.push(...leg.pts)
    for (const stub of existentialStubs(engine)) if (stub.wid === wire) points.push(stub.dot, stub.from, stub.to)
    const boundary = surface === 'draft'
      ? materializeComprehensionSnapshot(currentComprehensionDraft(this.#draft)).relation.boundary
      : this.#host.boundary()
    boundary.forEach((id, position) => {
      if (id !== wire) return
      const slot = resolvedFrameSlot(engine, position)
      if (slot !== null) points.push(slot.point)
    })
    const rect = canvas.getBoundingClientRect()
    const clients = points.map((point) => ({
      x: rect.left + (point.x * view.scale + view.offsetX) * rect.width / Math.max(1, canvas.width),
      y: rect.top + (point.y * view.scale + view.offsetY) * rect.height / Math.max(1, canvas.height),
    })).filter((point) => this.#host.mount.ownerDocument.elementFromPoint(point.x, point.y) === canvas)
    if (clients.length === 0) return null
    const center = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
    return clients.reduce((best, point) =>
      Math.hypot(point.x - center.x, point.y - center.y) < Math.hypot(best.x - center.x, best.y - center.y) ? point : best)
  }

  #worldToClient(canvas: HTMLCanvasElement, view: MutableView, world: Vec2): Vec2 {
    const rect = canvas.getBoundingClientRect()
    return {
      x: rect.left + (world.x * view.scale + view.offsetX) * rect.width / Math.max(1, canvas.width),
      y: rect.top + (world.y * view.scale + view.offsetY) * rect.height / Math.max(1, canvas.height),
    }
  }

  #pointerChanged(surface: SurfaceKind, client: Vec2): void {
    const endpoint = this.#endpointAtClient(client)
    if (surface === 'draft') {
      this.#draftHoverWire = endpoint?.kind === 'draft' ? endpoint.wire : null
      this.#hostHoverWire = null
    } else {
      this.#hostHoverWire = endpoint?.kind === 'host' ? endpoint.wire : null
      this.#draftHoverWire = null
    }
    this.#host.changed()
  }

  #hoverSource(): ComprehensionConnectionEndpoint | null {
    if (this.#draftHoverWire !== null) return { kind: 'draft', wire: this.#draftHoverWire }
    if (this.#hostHoverWire !== null) return { kind: 'host', wire: this.#hostHoverWire }
    return null
  }

  #connectionShapes(surface: SurfaceKind): Shape[] {
    const theme = this.#host.theme()
    const engine = surface === 'draft' ? this.#engine : this.#host.engine()
    const current = currentComprehensionDraft(this.#draft)
    const selectedDraft = new Set(this.#interaction.selection.filter((hit) => hit.kind === 'wire').map((hit) => hit.id))
    const selectedHost = new Set(this.#hostHoverWire === null ? [] : [this.#hostHoverWire])
    const presentation = deriveExternalReferencePresentation(current.externalWires, selectedDraft, selectedHost)
    const shapes: Shape[] = []
    const marked = surface === 'draft' ? presentation.markedDraft : presentation.markedHost
    const glowing = surface === 'draft' ? presentation.glowingDraft : presentation.glowingHost
    for (const wire of marked) shapes.push(...wireShapes(engine, wire, theme.interaction.hover, 2.2))
    for (const wire of glowing) shapes.push(...wireShapes(engine, wire, theme.interaction.hover, 3.5, theme.interaction.hover))
    const source = this.#connection?.source ?? this.#hoverSource()
    if (source === null) return shapes
    const targets = connectionTargets(this.#draft, source)
    const surfaceTargets = surface === 'draft' ? targets.draft : targets.host
    for (const wire of surfaceTargets) shapes.push(...wireShapes(engine, wire, theme.interaction.valid, 2.5))
    if (source.kind === surface) shapes.push(...wireShapes(engine, source.wire, theme.interaction.valid, 3))
    const active = this.#connection === null ? null : this.#endpointAtClient(this.#connection.current)
    if (active?.kind === surface && surfaceTargets.has(active.wire)) shapes.push(...wireShapes(engine, active.wire, theme.interaction.valid, 4, theme.interaction.valid))
    return shapes
  }

  #renderGesture(): void {
    this.#gesture.replaceChildren()
    const active = this.#connection
    if (active === null || !active.moved) return
    const line = this.#host.mount.ownerDocument.createElementNS('http://www.w3.org/2000/svg', 'line')
    line.setAttribute('x1', String(active.start.x)); line.setAttribute('y1', String(active.start.y))
    line.setAttribute('x2', String(active.current.x)); line.setAttribute('y2', String(active.current.y))
    line.classList.add('cursebreaker-construction-loupe__join-gesture')
    this.#gesture.append(line)
  }

  #regionAt(world: Vec2): RegionId {
    let best: { id: RegionId; radius: number } | null = null
    for (const [id, geometry] of this.#engine.regions) {
      if (this.#diagram().regions[id]?.kind === 'sheet') continue
      if (Math.hypot(world.x - geometry.center.x, world.y - geometry.center.y) <= geometry.radius
        && (best === null || geometry.radius < best.radius)) best = { id, radius: geometry.radius }
    }
    return best?.id ?? this.#diagram().root
  }

  #viewportSize(): { readonly width: number; readonly height: number } {
    return { width: this.#window.innerWidth, height: this.#window.innerHeight }
  }

  #resizeViewport = (): void => {
    if (this.#disposed) return
    this.#geometryVersion++
    this.#geometry = moveConstructionLoupe(this.#geometry, { x: 0, y: 0 }, this.#viewportSize())
    this.#applyGeometry()
  }

  #applyGeometry(): void {
    const aperture = loupeApertureRect(this.#geometry)
    this.#root.style.setProperty('--curse-loupe-rim-hit', `${loupeRimHitWidth(this.#geometry.diameter)}px`)
    Object.assign(this.#root.style, {
      left: `${aperture.left}px`, top: `${aperture.top}px`,
      width: `${aperture.width}px`, height: `${aperture.height}px`,
    })
  }

  #installMove(rim: HTMLElement): void {
    let drag: { pointer: number; start: Vec2; geometry: LoupeGeometry; version: number } | null = null
    rim.addEventListener('pointerdown', (event) => {
      if (hitConstructionLoupe(this.#geometry, { x: event.clientX, y: event.clientY }) !== 'rim') return
      drag = { pointer: event.pointerId, start: { x: event.clientX, y: event.clientY }, geometry: this.#geometry, version: this.#geometryVersion }
      rim.setPointerCapture(event.pointerId)
      event.preventDefault()
    })
    rim.addEventListener('pointermove', (event) => {
      if (drag?.pointer !== event.pointerId) return
      if (drag.version !== this.#geometryVersion) { drag = null; return }
      this.#geometry = moveConstructionLoupe(drag.geometry, {
        x: event.clientX - drag.start.x,
        y: event.clientY - drag.start.y,
      }, this.#viewportSize())
      this.#applyGeometry()
    })
    rim.addEventListener('pointerup', () => { drag = null })
    rim.addEventListener('pointercancel', () => { drag = null })
  }

  #installResize(handle: HTMLElement): void {
    let drag: { pointer: number; resize: ReturnType<typeof beginLoupeResize>; version: number } | null = null
    handle.addEventListener('pointerdown', (event) => {
      drag = { pointer: event.pointerId, resize: beginLoupeResize(this.#geometry), version: this.#geometryVersion }
      handle.setPointerCapture(event.pointerId)
      event.preventDefault()
    })
    handle.addEventListener('pointermove', (event) => {
      if (drag?.pointer !== event.pointerId) return
      if (drag.version !== this.#geometryVersion) { drag = null; return }
      this.#geometry = resizeConstructionLoupe(drag.resize, { x: event.clientX, y: event.clientY }, this.#viewportSize())
      this.#applyGeometry()
    })
    handle.addEventListener('pointerup', () => { drag = null })
    handle.addEventListener('pointercancel', () => { drag = null })
  }

  #centerClient(): Vec2 { return { ...this.#geometry.center } }
}
