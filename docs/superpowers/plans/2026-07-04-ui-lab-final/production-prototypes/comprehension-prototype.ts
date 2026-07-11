import type { Diagram, Endpoint, WireId } from '../kernel/diagram/diagram'
import { parseTerm } from '../kernel/term/parse'
import { verifyTheory } from '../kernel/proof/store'
import { buildFregeTheory } from '../theories/frege'
import type { Vec2 } from '../view/vec'
import { length, sub } from '../view/vec'
import type { Engine } from '../view/engine'
import { carryOver, mkEngine, resolvedFrameSlot, subtreeCarriers } from '../view/engine'
import { fitCamera, MIN_USER_ZOOM, normalizeUserZoom } from '../view/camera'
import type { Shape } from '../view/paint'
import { LIGHT, paint } from '../view/paint'
import { adaptCanvas, type CanvasAdapter } from '../view/canvas'
import { seedProject } from '../view/relax'
import {
  advanceInteractivePhysics,
  commitPhysicsDragSample,
  type ActivePhysicsDrag,
  type PhysicsDrag,
} from '../view/physics-drag'
import { existentialStubs, legPaths } from '../view/wires'
import type { Hit } from './hittest'
import { dragTarget, hitTest, wireHitTest } from './hittest'
import {
  addComprehensionRef,
  addComprehensionTerm,
  beginComprehensionDraft,
  cancelComprehensionDraft,
  commitComprehensionDraft,
  comprehensionFixture,
  currentComprehensionDraft,
  deleteComprehensionNode,
  applyComprehensionConnection,
  materializeComprehensionSnapshot,
  moveComprehensionHistory,
  planComprehensionConnection,
  severComprehensionEndpoint,
  ungraftComprehensionWire,
  wrapComprehensionNodes,
  type ComprehensionConnectionEndpoint,
  type ComprehensionDraft,
  type ComprehensionSnapshot,
  type ExternalWireBinding,
} from './comprehension-draft'

export type ComprehensionPrototype = { dispose(): void }

const CLICK_SLOP_PX = 3
const ZOOM_PER_WHEEL_PX = 0.001

type Viewport = {
  readonly canvas: HTMLCanvasElement
  readonly surface: CanvasAdapter
  diagram: Diagram
  boundary: readonly WireId[]
  engine: Engine
  view: { scale: number; offsetX: number; offsetY: number }
  userZoom: number
  cameraFocus: Vec2 | null
  selected: Hit | null
  hover: Hit | null
  pins: Set<string>
  activeDrag: ActivePhysicsDrag | null
}

type Surface = {
  readonly kind: ComprehensionConnectionEndpoint['kind']
  readonly viewport: Viewport
}

type PrimaryPointer = {
  readonly pointerId: number
  readonly surface: Surface
  readonly startClient: Vec2
  currentClient: Vec2
  moved: boolean
}

type PointerGesture =
  | (PrimaryPointer & { readonly kind: 'selection' })
  | (PrimaryPointer & { readonly kind: 'physics'; readonly drag: PhysicsDrag })
  | (PrimaryPointer & {
      readonly kind: 'connection'
      readonly source: ComprehensionConnectionEndpoint
      readonly snapshot: ComprehensionSnapshot
    })
  | {
      readonly kind: 'slash'
      readonly pointerId: number
      readonly surface: Surface
      readonly startClient: Vec2
      currentClient: Vec2
    }

export type ExternalReferencePresentation = {
  readonly markedDraft: ReadonlySet<WireId>
  readonly markedHost: ReadonlySet<WireId>
  readonly glowingDraft: ReadonlySet<WireId>
  readonly glowingHost: ReadonlySet<WireId>
}

/** Derive the complete visual identity relation from canonical bindings.
    Each host has one draft representative; one draft may identify several
    distinct host wires, and activation of any member highlights that star. */
export function deriveExternalReferencePresentation(
  bindings: readonly ExternalWireBinding[],
  activeDraft: ReadonlySet<WireId>,
  activeHost: ReadonlySet<WireId>,
): ExternalReferencePresentation {
  const markedDraft = new Set(bindings.map((binding) => binding.draftWire))
  const markedHost = new Set(bindings.map((binding) => binding.hostWire))
  const glowingDraft = new Set([...activeDraft].filter((wire) => markedDraft.has(wire)))
  for (const binding of bindings) if (activeHost.has(binding.hostWire)) glowingDraft.add(binding.draftWire)
  const glowingHost = new Set(bindings
    .filter((binding) => glowingDraft.has(binding.draftWire))
    .map((binding) => binding.hostWire))
  return { markedDraft, markedHost, glowingDraft, glowingHost }
}

function element<K extends keyof HTMLElementTagNameMap>(tag: K, className: string, text = ''): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag)
  node.className = className
  node.textContent = text
  return node
}

function localPointAtClient(canvas: HTMLCanvasElement, client: Vec2): Vec2 {
  const rect = canvas.getBoundingClientRect()
  return {
    x: (client.x - rect.left) * canvas.width / rect.width,
    y: (client.y - rect.top) * canvas.height / rect.height,
  }
}

function localPoint(canvas: HTMLCanvasElement, event: PointerEvent | WheelEvent): Vec2 {
  return localPointAtClient(canvas, { x: event.clientX, y: event.clientY })
}

function worldPoint(viewport: Viewport, screen: Vec2): Vec2 {
  return {
    x: (screen.x - viewport.view.offsetX) / viewport.view.scale,
    y: (screen.y - viewport.view.offsetY) / viewport.view.scale,
  }
}

function worldAtClient(viewport: Viewport, client: Vec2): Vec2 {
  return worldPoint(viewport, localPointAtClient(viewport.canvas, client))
}

function clientAtWorld(viewport: Viewport, point: Vec2): Vec2 {
  const rect = viewport.canvas.getBoundingClientRect()
  const local = {
    x: point.x * viewport.view.scale + viewport.view.offsetX,
    y: point.y * viewport.view.scale + viewport.view.offsetY,
  }
  return {
    x: rect.left + local.x * rect.width / viewport.canvas.width,
    y: rect.top + local.y * rect.height / viewport.canvas.height,
  }
}

function fitViewport(viewport: Viewport): void {
  const frame = viewport.engine.frame
  const { width, height } = viewport.surface.size()
  viewport.view = fitCamera(
    frame === null ? undefined : { center: frame.center, radius: frame.half },
    width,
    height,
    viewport.userZoom,
  )
  if (viewport.cameraFocus !== null) {
    viewport.view.offsetX = width / 2 - viewport.cameraFocus.x * viewport.view.scale
    viewport.view.offsetY = height / 2 - viewport.cameraFocus.y * viewport.view.scale
  }
}

function hitShapes(viewport: Viewport, hit: Hit, stroke: string, width: number, glow: string | null): Shape[] {
  if (hit.kind === 'node') {
    const body = viewport.engine.bodies.get(hit.id)
    return body === undefined ? [] : [{
      kind: 'circle', center: body.pos, r: body.discR * viewport.engine.scale + 1,
      fill: null, stroke, width, insetColor: null, glow,
    }]
  }
  if (hit.kind === 'region') {
    const region = viewport.engine.regions.get(hit.id)
    return region === undefined ? [] : [{
      kind: 'circle', center: region.center, r: region.radius + 0.8,
      fill: null, stroke, width, insetColor: null, glow,
    }]
  }
  const shapes: Shape[] = []
  for (const leg of legPaths(viewport.engine)) {
    if (leg.wid === hit.id) shapes.push({ kind: 'polyline', pts: leg.pts, stroke, width, glow })
  }
  for (const stub of existentialStubs(viewport.engine)) {
    if (stub.wid === hit.id) shapes.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width, glow })
  }
  return shapes
}

function grabAt(viewport: Viewport, world: Vec2): PhysicsDrag | null {
  const target = dragTarget(viewport.engine, world, { scale: viewport.view.scale })
  if (target === null) return null
  const ids = target.kind === 'body' ? [target.id] : subtreeCarriers(viewport.engine, target.id)
  const bodies = new Map<string, Vec2>()
  const origins = new Map<string, Vec2>()
  for (const id of ids) {
    const body = viewport.engine.bodies.get(id)
    if (body !== undefined) {
      bodies.set(id, { x: body.pos.x - world.x, y: body.pos.y - world.y })
      origins.set(id, { ...body.pos })
    }
  }
  return bodies.size === 0 ? null : { bodies, origins }
}

function movePhysicsDrag(viewport: Viewport, drag: PhysicsDrag, screen: Vec2): void {
  const active = { drag, cursor: worldPoint(viewport, screen) }
  viewport.activeDrag = active
  commitPhysicsDragSample(viewport.engine, active)
}

function finishPhysicsDrag(viewport: Viewport, drag: PhysicsDrag, screen: Vec2, pinOnRelease: boolean): void {
  const active = { drag, cursor: worldPoint(viewport, screen) }
  viewport.activeDrag = active
  commitPhysicsDragSample(viewport.engine, active)
  if (pinOnRelease && drag.bodies.size === 1) {
    const id = drag.bodies.keys().next().value as string | undefined
    if (id !== undefined && viewport.diagram.nodes[id] !== undefined) viewport.pins.add(id)
  }
  viewport.activeDrag = null
}

function makeViewport(
  canvas: HTMLCanvasElement,
  diagram: Diagram,
  boundary: readonly WireId[],
): Viewport {
  const surface = adaptCanvas(canvas)
  const engine = mkEngine(diagram, boundary)
  seedProject(engine)
  const viewport: Viewport = {
    canvas, surface, diagram, boundary, engine,
    view: { scale: 1, offsetX: 0, offsetY: 0 }, userZoom: 1, cameraFocus: null,
    selected: null, hover: null, pins: new Set(), activeDrag: null,
  }
  canvas.addEventListener('wheel', (event) => {
    event.preventDefault()
    const screen = localPoint(canvas, event)
    const underCursor = worldPoint(viewport, screen)
    viewport.userZoom = normalizeUserZoom(viewport.userZoom * Math.exp(-event.deltaY * ZOOM_PER_WHEEL_PX))
    if (viewport.userZoom === MIN_USER_ZOOM) {
      viewport.cameraFocus = null
      fitViewport(viewport)
      return
    }
    const frame = viewport.engine.frame
    const { width, height } = viewport.surface.size()
    const scale = fitCamera(
      frame === null ? undefined : { center: frame.center, radius: frame.half },
      width, height, viewport.userZoom,
    ).scale
    viewport.cameraFocus = {
      x: underCursor.x - (screen.x - width / 2) / scale,
      y: underCursor.y - (screen.y - height / 2) / scale,
    }
    fitViewport(viewport)
  }, { passive: false })
  return viewport
}

function syncViewport(viewport: Viewport, diagram: Diagram, boundary: readonly WireId[], placed?: { readonly node: string; readonly at: Vec2 }): void {
  const previous = viewport.engine
  const next = mkEngine(diagram, boundary)
  carryOver(previous, next)
  if (placed !== undefined) {
    const body = next.bodies.get(placed.node)
    if (body !== undefined) {
      // Placement participates in the canonical natural-layout rebuild. The
      // previous viewport point is unscaled exactly as carryOver unscales
      // surviving bodies; seedProject then owns overlap resolution, content
      // scaling, frame clamping, and region recomputation for the whole result.
      const frame = previous.frame
      const scale = Number.isFinite(previous.scale) && previous.scale > 0 ? previous.scale : 1
      body.pos = frame === null
        ? { ...placed.at }
        : {
            x: frame.center.x + (placed.at.x - frame.center.x) / scale,
            y: frame.center.y + (placed.at.y - frame.center.y) / scale,
          }
    }
  }
  seedProject(next)
  viewport.diagram = diagram
  viewport.boundary = boundary
  viewport.engine = next
  viewport.selected = null
  viewport.hover = null
  for (const id of [...viewport.pins]) if (diagram.nodes[id] === undefined) viewport.pins.delete(id)
}

function renderViewport(
  viewport: Viewport,
  advance: boolean,
  highlights: readonly { readonly hit: Hit; readonly stroke: string; readonly width: number; readonly glow?: string | null }[],
  hoverStroke = '#2563eb',
): void {
  if (!viewport.surface.syncSize()) return
  advanceInteractivePhysics(viewport.engine, viewport.pins, viewport.activeDrag, advance)
  fitViewport(viewport)
  const shapes = paint(viewport.engine, LIGHT)
  for (const highlight of highlights) shapes.push(...hitShapes(viewport, highlight.hit, highlight.stroke, highlight.width, highlight.glow ?? null))
  if (viewport.hover !== null) shapes.push(...hitShapes(viewport, viewport.hover, hoverStroke, 1.7, null))
  viewport.surface.render(shapes, viewport.view)
}

function wireClientPoint(viewport: Viewport, wire: WireId, toward: Vec2): Vec2 | null {
  const points: Vec2[] = []
  for (const leg of legPaths(viewport.engine)) if (leg.wid === wire) points.push(...leg.pts)
  for (const stub of existentialStubs(viewport.engine)) if (stub.wid === wire) points.push(stub.from, stub.to)
  viewport.boundary.forEach((wid, position) => {
    if (wid !== wire) return
    const slot = resolvedFrameSlot(viewport.engine, position)
    if (slot !== null) points.push(slot.point)
  })
  if (points.length === 0) return null
  const clients = points.flatMap((point) => {
    const client = clientAtWorld(viewport, point)
    if (document.elementFromPoint(client.x, client.y) !== viewport.canvas) return []
    const hit = wireHitTest(viewport.engine, point, { scale: viewport.view.scale })
    return hit?.id === wire ? [client] : []
  })
  if (clients.length === 0) return null
  return clients.reduce((best, point) => length(sub(point, toward)) < length(sub(best, toward)) ? point : best)
}

function segmentsCross(a: Vec2, b: Vec2, c: Vec2, d: Vec2): boolean {
  const side = (p: Vec2, q: Vec2, r: Vec2): number => (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)
  return side(a, b, c) * side(a, b, d) <= 0 && side(c, d, a) * side(c, d, b) <= 0
}

function promptAt(client: Vec2, placeholder: string, commit: (value: string) => void): void {
  const input = element('input', 'comp-inline-input')
  input.placeholder = placeholder
  input.style.left = `${client.x}px`
  input.style.top = `${client.y}px`
  document.body.append(input)
  const close = (): void => { input.remove() }
  input.addEventListener('keydown', (event) => {
    event.stopPropagation()
    if (event.key === 'Enter') {
      try { commit(input.value); close() } catch { input.focus() }
    } else if (event.key === 'Escape') close()
  })
  input.addEventListener('blur', close)
  requestAnimationFrame(() => input.focus())
}

export function mountComprehensionPrototype(host: HTMLElement): ComprehensionPrototype {
  const fixture = comprehensionFixture()
  const proofContext = verifyTheory(buildFregeTheory())
  let hostDiagram = fixture.diagram
  let draft: ComprehensionDraft | null = null
  let selectedDraft: Hit[] = []
  let pointerGesture: PointerGesture | null = null
  let draftWireHover: WireId | null = null
  let hostWireHover: WireId | null = null
  let disposed = false
  let raf = 0

  host.replaceChildren()
  host.className = 'comp-root'
  const mode = element('div', 'comp-mode', 'PROVING FORWARD')
  const proofCanvas = element('canvas', 'comp-canvas proof-canvas')
  const hint = element('div', 'comp-hint', 'Still right-click the selected relation bubble to choose a substitution.')
  const status = element('div', 'comp-status', 'Target selected · the proof has not changed')
  const menuLayer = element('div', 'comp-menu-layer')
  const gestureSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
  gestureSvg.classList.add('comp-gesture-layer')
  const editor = element('section', 'comp-editor')
  editor.hidden = true
  const title = element('header', 'comp-editor-title')
  const titleText = element('strong', '', 'SUBSTITUTE R/2 · NEW RELATION')
  const editorActions = element('span', 'comp-editor-actions')
  const undo = element('button', '', 'Undo')
  const redo = element('button', '', 'Redo')
  const cancel = element('button', '', 'Cancel')
  const instantiate = element('button', 'is-primary', 'Instantiate')
  for (const button of [undo, redo, cancel, instantiate]) button.type = 'button'
  editorActions.append(undo, redo, cancel, instantiate)
  title.append(titleText, editorActions)
  const editorCanvas = element('canvas', 'comp-canvas editor-canvas')
  const resize = element('div', 'comp-resize')
  editor.append(title, editorCanvas, resize)
  host.append(proofCanvas, editor, gestureSvg, mode, hint, status, menuLayer)

  const proofView = makeViewport(proofCanvas, hostDiagram, [])
  proofView.selected = { kind: 'region', id: fixture.bubble }
  const initialDraft = beginComprehensionDraft(hostDiagram, fixture.bubble)
  const initialSnapshot = currentComprehensionDraft(initialDraft)
  const initialMaterialized = materializeComprehensionSnapshot(initialSnapshot)
  const editorView = makeViewport(editorCanvas, initialMaterialized.relation.diagram, initialMaterialized.relation.boundary)
  const proofSurface: Surface = { kind: 'host', viewport: proofView }
  const draftSurface: Surface = { kind: 'draft', viewport: editorView }
  const selectDraft = (hit: Hit | null): void => {
    editorView.selected = hit
    if (hit === null) { selectedDraft = []; return }
    const index = selectedDraft.findIndex((value) => value.kind === hit.kind && value.id === hit.id)
    if (index >= 0) selectedDraft.splice(index, 1)
    else selectedDraft.push(hit)
    status.textContent = `${selectedDraft.length} selected in the draft`
  }

  const clearPointerGesture = (): void => {
    const active = pointerGesture
    pointerGesture = null
    if (active === null) return
    active.surface.viewport.activeDrag = null
    const canvas = active.surface.viewport.canvas
    if (canvas.hasPointerCapture(active.pointerId)) canvas.releasePointerCapture(active.pointerId)
  }

  const connectionTargets = (source: ComprehensionConnectionEndpoint): { readonly draft: ReadonlySet<WireId>; readonly host: ReadonlySet<WireId> } => {
    const draftTargets = new Set<WireId>()
    const hostTargets = new Set<WireId>()
    if (draft === null) return { draft: draftTargets, host: hostTargets }
    const current = currentComprehensionDraft(draft)
    for (const wire of Object.keys(current.relation.diagram.wires)) {
      if (planComprehensionConnection(draft, source, { kind: 'draft', wire }).ok) draftTargets.add(wire)
    }
    for (const wire of Object.keys(draft.host.wires)) {
      if (planComprehensionConnection(draft, source, { kind: 'host', wire }).ok) hostTargets.add(wire)
    }
    return { draft: draftTargets, host: hostTargets }
  }

  const connectionEndpointAt = (client: Vec2): ComprehensionConnectionEndpoint | null => {
    const top = document.elementFromPoint(client.x, client.y)
    if (top === editorCanvas) {
      const hit = wireHitTest(editorView.engine, worldAtClient(editorView, client), { scale: editorView.view.scale })
      return hit === null ? null : { kind: 'draft', wire: hit.id }
    }
    if (top === proofCanvas) {
      const hit = wireHitTest(proofView.engine, worldAtClient(proofView, client), { scale: proofView.view.scale })
      return hit === null ? null : { kind: 'host', wire: hit.id }
    }
    return null
  }

  const report = (action: () => void, success: string): boolean => {
    try {
      action()
      status.textContent = success
      return true
    } catch (error) {
      status.textContent = `Refused: ${error instanceof Error ? error.message : String(error)}`
      return false
    }
  }

  const refreshDraft = (placed?: { readonly node: string; readonly at: Vec2 }): void => {
    if (draft === null) return
    clearPointerGesture()
    draftWireHover = null
    hostWireHover = null
    const current = currentComprehensionDraft(draft)
    const materialized = materializeComprehensionSnapshot(current)
    syncViewport(editorView, materialized.relation.diagram, materialized.relation.boundary, placed)
    selectedDraft = []
    undo.disabled = draft.cursor === 0
    redo.disabled = draft.cursor === draft.history.length - 1
  }

  const mutate = (change: (value: ComprehensionDraft) => ComprehensionDraft, message: string, placedAt?: Vec2): boolean => {
    let placed: { readonly node: string; readonly at: Vec2 } | undefined
    return report(() => {
      if (draft === null) throw new Error('no comprehension transaction is open')
      const before = new Set(Object.keys(currentComprehensionDraft(draft).relation.diagram.nodes))
      draft = change(draft)
      if (placedAt !== undefined) {
        const node = Object.keys(currentComprehensionDraft(draft).relation.diagram.nodes).find((id) => !before.has(id))
        if (node !== undefined) placed = { node, at: placedAt }
      }
      refreshDraft(placed)
    }, message)
  }

  const closeMenus = (): void => { menuLayer.replaceChildren() }

  const openFormulaCascade = (client: Vec2, world: Vec2): void => {
    closeMenus()
    if (draft === null) return
    const box = element('div', 'comp-cascade')
    box.style.left = `${Math.min(client.x, innerWidth - 260)}px`
    box.style.top = `${Math.min(client.y, innerHeight - 330)}px`
    const search = element('input', '')
    search.placeholder = 'spawn formula…'
    const list = element('div', 'comp-cascade-list')
    box.append(search, list)
    const row = (label: string, hintText: string, action: () => void): HTMLElement => {
      const item = element('button', 'comp-cascade-row')
      item.type = 'button'
      item.append(element('span', '', label), element('small', '', hintText))
      item.addEventListener('click', () => { closeMenus(); action() })
      return item
    }
    const rebuild = (): void => {
      const query = search.value.trim().toLowerCase()
      const rows: HTMLElement[] = [row('λ term…', '', () => {
        promptAt(client, 'λ-term, e.g. \\x. x', (source) => {
          if (mutate((value) => addComprehensionTerm(value, parseTerm(source)), 'Term added through the formula editor.', world)) closeMenus()
        })
      })]
      for (const [name, relation] of proofContext.relations) {
        if (query !== '' && !name.toLowerCase().includes(query)) continue
        rows.push(row(name, `/${relation.boundary.length}`, () => {
          mutate((value) => addComprehensionRef(value, name, relation.boundary.length), `${name}/${relation.boundary.length} added.`, world)
        }))
      }
      list.replaceChildren(...rows)
    }
    search.addEventListener('input', rebuild)
    search.addEventListener('keydown', (event) => { event.stopPropagation(); if (event.key === 'Escape') closeMenus() })
    rebuild()
    menuLayer.append(box)
    requestAnimationFrame(() => search.focus())
  }

  const openEditor = (invocation?: Vec2): void => {
    closeMenus()
    clearPointerGesture()
    draftWireHover = null
    hostWireHover = null
    draft = beginComprehensionDraft(hostDiagram, fixture.bubble)
    refreshDraft()
    editor.hidden = false
    const bubble = proofView.engine.regions.get(fixture.bubble)
    if (bubble === undefined) throw new Error('the target bubble is not rendered')
    const center = invocation ?? clientAtWorld(proofView, bubble.center)
    const width = Math.min(660, innerWidth - 40)
    const height = Math.min(560, innerHeight - 70)
    const right = center.x + 16
    const left = right + width <= innerWidth - 12 ? right : center.x - width - 16
    editor.style.left = `${Math.max(12, Math.min(innerWidth - width - 12, left))}px`
    editor.style.top = `${Math.max(44, Math.min(innerHeight - height - 34, center.y - 18))}px`
    editor.style.width = `${width}px`
    editor.style.height = `${height}px`
    editor.animate([
      { transform: 'scale(.18)', borderRadius: '50%', opacity: .35 },
      { transform: 'scale(1)', borderRadius: '12px', opacity: 1 },
    ], { duration: 240, easing: 'cubic-bezier(.2,.8,.2,1)' })
    hint.textContent = 'Right-click inside to spawn · drag any line to an eligible line on either surface · right-drag slashes · W wraps'
    status.textContent = 'Draft opened beside the invocation point; drag the title or resize from the corner at any time.'
  }

  const openProofMenu = (client: Vec2): void => {
    closeMenus()
    const box = element('div', 'comp-proof-menu')
    box.style.left = `${client.x}px`
    box.style.top = `${client.y}px`
    box.append(element('div', 'comp-menu-heading', 'APPLICABLE HERE'))
    const named = element('button', '', 'Instantiate with named relation…')
    named.disabled = true
    const anonymous = element('button', 'is-primary', 'Instantiate with new relation…')
    anonymous.addEventListener('click', () => openEditor(client))
    box.append(anonymous, named)
    menuLayer.append(box)
  }

  proofCanvas.addEventListener('contextmenu', (event) => {
    event.preventDefault()
    if (draft !== null || hostDiagram.regions[fixture.bubble] === undefined) return
    const bubble = proofView.engine.regions.get(fixture.bubble)
    if (bubble === undefined) return
    const point = worldAtClient(proofView, { x: event.clientX, y: event.clientY })
    if (length(sub(point, bubble.center)) <= bubble.radius) openProofMenu({ x: event.clientX, y: event.clientY })
    else status.textContent = 'Still right-click the selected relation bubble.'
  })

  editorCanvas.addEventListener('contextmenu', (event) => { event.preventDefault() })

  const refreshHoverAt = (client: Vec2): void => {
    const top = document.elementFromPoint(client.x, client.y)
    const update = (surface: Surface): void => {
      const world = worldAtClient(surface.viewport, client)
      surface.viewport.hover = hitTest(surface.viewport.engine, world, { scale: surface.viewport.view.scale })
      const wire = wireHitTest(surface.viewport.engine, world, { scale: surface.viewport.view.scale })?.id ?? null
      if (surface.kind === 'draft') {
        draftWireHover = wire
        hostWireHover = null
        proofView.hover = null
      } else {
        hostWireHover = wire
        draftWireHover = null
        editorView.hover = null
      }
    }
    if (top === editorCanvas && draft !== null) update(draftSurface)
    else if (top === proofCanvas) update(proofSurface)
    else {
      draftWireHover = null
      hostWireHover = null
      editorView.hover = null
      proofView.hover = null
    }
  }

  const selectAt = (surface: Surface, client: Vec2): void => {
    const world = worldAtClient(surface.viewport, client)
    const hit = hitTest(surface.viewport.engine, world, { scale: surface.viewport.view.scale })
    if (surface.kind === 'draft') {
      const selected = hit !== null && hit.kind === editorView.selected?.kind && hit.id === editorView.selected.id ? null : hit
      selectDraft(selected)
      return
    }
    proofView.selected = hit !== null && hit.kind === proofView.selected?.kind && hit.id === proofView.selected.id ? null : hit
  }

  const onPointerDown = (surface: Surface, event: PointerEvent): void => {
    if (pointerGesture !== null) return
    const client = { x: event.clientX, y: event.clientY }
    if (event.button === 2 && surface.kind === 'draft' && draft !== null) {
      pointerGesture = {
        kind: 'slash', pointerId: event.pointerId, surface,
        startClient: client, currentClient: client,
      }
      surface.viewport.canvas.setPointerCapture(event.pointerId)
      return
    }
    if (event.button !== 0) return

    const world = worldAtClient(surface.viewport, client)
    const drag = event.ctrlKey ? grabAt(surface.viewport, world) : null
    const wire = !event.ctrlKey && draft !== null
      ? wireHitTest(surface.viewport.engine, world, { scale: surface.viewport.view.scale })?.id ?? null
      : null
    const base = {
      pointerId: event.pointerId,
      surface,
      startClient: client,
      currentClient: client,
      moved: false,
    }
    pointerGesture = drag !== null
      ? { ...base, kind: 'physics', drag }
      : wire !== null && draft !== null
        ? { ...base, kind: 'connection', source: { kind: surface.kind, wire }, snapshot: currentComprehensionDraft(draft) }
        : { ...base, kind: 'selection' }
    surface.viewport.canvas.setPointerCapture(event.pointerId)
  }

  const onPointerMove = (event: PointerEvent): void => {
    if (pointerGesture !== null && pointerGesture.pointerId !== event.pointerId) return
    const client = { x: event.clientX, y: event.clientY }
    refreshHoverAt(client)
    const gesture = pointerGesture
    if (gesture === null || gesture.pointerId !== event.pointerId) return
    gesture.currentClient = client
    if (gesture.kind === 'slash') return
    if (gesture.kind === 'connection' && (draft === null || currentComprehensionDraft(draft) !== gesture.snapshot)) {
      clearPointerGesture()
      status.textContent = 'Connection cancelled because the draft changed.'
      return
    }
    const justMoved = !gesture.moved && length(sub(client, gesture.startClient)) > CLICK_SLOP_PX
    if (justMoved) {
      gesture.moved = true
      if (gesture.kind === 'physics') {
        for (const id of gesture.drag.bodies.keys()) gesture.surface.viewport.pins.delete(id)
      }
    }
    if (gesture.moved && gesture.kind === 'physics') {
      movePhysicsDrag(gesture.surface.viewport, gesture.drag, localPointAtClient(gesture.surface.viewport.canvas, client))
    }
  }

  const finishSlash = (gesture: Extract<PointerGesture, { kind: 'slash' }>): void => {
    const moved = length(sub(gesture.currentClient, gesture.startClient)) > CLICK_SLOP_PX
    if (!moved) {
      openFormulaCascade(gesture.startClient, worldAtClient(editorView, gesture.startClient))
      return
    }
    if (draft === null) return
    const a = worldAtClient(editorView, gesture.startClient)
    const b = worldAtClient(editorView, gesture.currentClient)
    for (const leg of legPaths(editorView.engine)) {
      if (!leg.pts.some((point, index) => index > 0 && segmentsCross(a, b, leg.pts[index - 1]!, point))) continue
      const binding = currentComprehensionDraft(draft).externalWires.find((value) => value.draftWire === leg.wid)
      if (binding !== undefined) {
        mutate((value) => ungraftComprehensionWire(value, leg.wid), 'External references severed from this identity; the draft line remains local.')
        return
      }
      const wire = currentComprehensionDraft(draft).relation.diagram.wires[leg.wid]
      const endpoint: Endpoint | undefined = wire?.endpoints[0]
      if (endpoint !== undefined) mutate((value) => severComprehensionEndpoint(value, leg.wid, endpoint), 'Strand severed.')
      return
    }
    status.textContent = 'The slash crossed no strand.'
  }

  const onPointerUp = (event: PointerEvent): void => {
    const gesture = pointerGesture
    if (gesture === null || gesture.pointerId !== event.pointerId) return
    gesture.currentClient = { x: event.clientX, y: event.clientY }

    if (gesture.kind === 'slash') {
      clearPointerGesture()
      finishSlash(gesture)
      return
    }
    if (gesture.kind === 'physics') {
      if (gesture.moved) {
        finishPhysicsDrag(
          gesture.surface.viewport,
          gesture.drag,
          localPointAtClient(gesture.surface.viewport.canvas, gesture.currentClient),
          !event.ctrlKey,
        )
      } else selectAt(gesture.surface, gesture.currentClient)
      clearPointerGesture()
      return
    }
    if (gesture.kind === 'selection' || !gesture.moved) {
      clearPointerGesture()
      selectAt(gesture.surface, gesture.currentClient)
      return
    }
    if (draft === null || currentComprehensionDraft(draft) !== gesture.snapshot) {
      clearPointerGesture()
      status.textContent = 'Connection cancelled because the draft changed.'
      return
    }

    const target = connectionEndpointAt(gesture.currentClient)
    const source = gesture.source
    clearPointerGesture()
    if (target === null) {
      status.textContent = 'Release on an eligible line on the other surface or in the draft.'
      return
    }
    const plan = planComprehensionConnection(draft, source, target)
    if (!plan.ok) {
      status.textContent = `Refused: ${plan.message}`
      return
    }
    const message = plan.kind === 'local-fusion'
      ? 'Lines joined — one individual now.'
      : 'The added boundary edge now shares the highlighted host identity.'
    mutate((value) => applyComprehensionConnection(value, source, target), message)
  }

  const cancelPointerGesture = (event: PointerEvent): void => {
    const gesture = pointerGesture
    if (gesture === null || gesture.pointerId !== event.pointerId) return
    const activeConnection = gesture.kind === 'connection' && gesture.moved
    clearPointerGesture()
    if (activeConnection) status.textContent = 'Connection cancelled.'
  }

  for (const surface of [proofSurface, draftSurface]) {
    const canvas = surface.viewport.canvas
    canvas.addEventListener('pointerdown', (event) => onPointerDown(surface, event))
    canvas.addEventListener('pointermove', onPointerMove)
    canvas.addEventListener('pointerleave', (event) => refreshHoverAt({ x: event.clientX, y: event.clientY }))
    canvas.addEventListener('pointerup', onPointerUp)
    canvas.addEventListener('pointercancel', cancelPointerGesture)
    canvas.addEventListener('lostpointercapture', cancelPointerGesture)
  }

  const moveHistory = (delta: number): void => {
    mutate((value) => moveComprehensionHistory(value, delta), delta < 0 ? 'Draft undo.' : 'Draft redo.')
  }
  undo.addEventListener('click', () => moveHistory(-1))
  redo.addEventListener('click', () => moveHistory(1))
  cancel.addEventListener('click', () => {
    report(() => {
      if (draft === null) throw new Error('no draft is open')
      hostDiagram = cancelComprehensionDraft(draft)
      draft = null
      editor.hidden = true
      selectedDraft = []
      clearPointerGesture()
      draftWireHover = null
      hostWireHover = null
      hint.textContent = 'Still right-click the selected relation bubble to choose a substitution.'
    }, 'Cancelled. The proof and its view are exactly unchanged.')
  })
  instantiate.addEventListener('click', () => {
    report(() => {
      if (draft === null) throw new Error('no draft is open')
      hostDiagram = commitComprehensionDraft(draft)
      draft = null
      editor.hidden = true
      selectedDraft = []
      clearPointerGesture()
      draftWireHover = null
      hostWireHover = null
      proofView.selected = null
      syncViewport(proofView, hostDiagram, [])
      hint.textContent = 'Instantiation committed as one checked proof step. Reload to run the comparison again.'
    }, 'Committed one kernel-checked comprehension step; the target bubble was dissolved.')
  })

  let movingWindow: { start: Vec2; left: number; top: number } | null = null
  title.addEventListener('pointerdown', (event) => {
    if (event.target instanceof HTMLButtonElement) return
    movingWindow = { start: { x: event.clientX, y: event.clientY }, left: editor.offsetLeft, top: editor.offsetTop }
    title.setPointerCapture(event.pointerId)
  })
  title.addEventListener('pointermove', (event) => {
    if (movingWindow === null) return
    editor.style.left = `${Math.max(0, Math.min(innerWidth - editor.offsetWidth, movingWindow.left + event.clientX - movingWindow.start.x))}px`
    editor.style.top = `${Math.max(0, Math.min(innerHeight - editor.offsetHeight - 26, movingWindow.top + event.clientY - movingWindow.start.y))}px`
  })
  title.addEventListener('pointerup', () => { movingWindow = null })

  let resizing: { start: Vec2; width: number; height: number } | null = null
  resize.addEventListener('pointerdown', (event) => {
    resizing = { start: { x: event.clientX, y: event.clientY }, width: editor.offsetWidth, height: editor.offsetHeight }
    resize.setPointerCapture(event.pointerId)
    event.preventDefault()
  })
  resize.addEventListener('pointermove', (event) => {
    if (resizing === null) return
    editor.style.width = `${Math.max(420, Math.min(innerWidth - editor.offsetLeft, resizing.width + event.clientX - resizing.start.x))}px`
    editor.style.height = `${Math.max(340, Math.min(innerHeight - editor.offsetTop - 26, resizing.height + event.clientY - resizing.start.y))}px`
  })
  resize.addEventListener('pointerup', () => { resizing = null })

  window.addEventListener('pointerdown', (event) => {
    if (event.target instanceof Node && !menuLayer.contains(event.target)) closeMenus()
  }, { capture: true })
  const onKey = (event: KeyboardEvent): void => {
    if (document.activeElement instanceof HTMLInputElement || draft === null) return
    if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 'z') {
      event.preventDefault(); moveHistory(event.shiftKey ? 1 : -1)
    } else if (event.key === 'Escape') cancel.click()
    else if (event.key === 'Enter' && event.ctrlKey) instantiate.click()
    else if (event.key.toLowerCase() === 'j') {
      const wires = selectedDraft.filter((hit): hit is Extract<Hit, { kind: 'wire' }> => hit.kind === 'wire')
      if (wires.length < 2) { status.textContent = 'Select at least two draft lines to join.'; return }
      let first = wires[0]!.id
      for (const wire of wires.slice(1)) {
        const target = wire.id
        if (!mutate((value) => applyComprehensionConnection(
          value,
          { kind: 'draft', wire: first },
          { kind: 'draft', wire: target },
        ), 'Selected lines joined.')) return
        if (currentComprehensionDraft(draft!).relation.diagram.wires[first] === undefined) first = target
      }
    } else if (event.key.toLowerCase() === 'w') {
      const nodes = selectedDraft.filter((hit): hit is Extract<Hit, { kind: 'node' }> => hit.kind === 'node').map((hit) => hit.id)
      mutate((value) => wrapComprehensionNodes(value, nodes, event.shiftKey ? 1 : null), event.shiftKey ? 'Bubble wrapped around the selection.' : 'Cut drawn around the selection.')
    } else if (event.key === 'Delete' || event.key === 'Backspace') {
      const nodes = selectedDraft.filter((hit): hit is Extract<Hit, { kind: 'node' }> => hit.kind === 'node').map((hit) => hit.id)
      if (nodes.length === 0) { status.textContent = 'Select formula nodes to delete; formal boundary lines are protected.'; return }
      for (const node of nodes) if (!mutate((value) => deleteComprehensionNode(value, node), 'Selected formula content deleted.')) break
    }
  }
  window.addEventListener('keydown', onKey)

  const svgLine = (from: Vec2, to: Vec2, className: string): SVGLineElement => {
    const line = document.createElementNS('http://www.w3.org/2000/svg', 'line')
    line.setAttribute('x1', String(from.x)); line.setAttribute('y1', String(from.y))
    line.setAttribute('x2', String(to.x)); line.setAttribute('y2', String(to.y))
    line.setAttribute('class', className)
    return line
  }

  const externalPresentation = (): ExternalReferencePresentation => {
    if (draft === null) return deriveExternalReferencePresentation([], new Set(), new Set())
    const activeDraft = new Set<WireId>()
    for (const hit of selectedDraft) if (hit.kind === 'wire') activeDraft.add(hit.id)
    if (editorView.hover?.kind === 'wire') activeDraft.add(editorView.hover.id)
    if (draftWireHover !== null) activeDraft.add(draftWireHover)
    const activeHost = new Set<WireId>()
    if (proofView.selected?.kind === 'wire') activeHost.add(proofView.selected.id)
    if (proofView.hover?.kind === 'wire') activeHost.add(proofView.hover.id)
    if (hostWireHover !== null) activeHost.add(hostWireHover)
    return deriveExternalReferencePresentation(currentComprehensionDraft(draft).externalWires, activeDraft, activeHost)
  }

  const connectionDisplay = (): {
    readonly source: ComprehensionConnectionEndpoint | null
    readonly dragging: boolean
    readonly draftTargets: ReadonlySet<WireId>
    readonly hostTargets: ReadonlySet<WireId>
    readonly activeTarget: ComprehensionConnectionEndpoint | null
  } => {
    const connectionGesture = pointerGesture?.kind === 'connection' ? pointerGesture : null
    const active = connectionGesture?.moved ? connectionGesture : null
    const hoverSource: ComprehensionConnectionEndpoint | null = pointerGesture !== null || draft === null
      ? null
      : draftWireHover !== null
        ? { kind: 'draft', wire: draftWireHover }
        : hostWireHover !== null
          ? { kind: 'host', wire: hostWireHover }
          : null
    const source = connectionGesture?.source ?? hoverSource
    const targets = source === null ? { draft: new Set<WireId>(), host: new Set<WireId>() } : connectionTargets(source)
    const target = active === null ? null : connectionEndpointAt(active.currentClient)
    const accepted = source === null || target === null || draft === null
      ? null
      : planComprehensionConnection(draft, source, target)
    return {
      source,
      dragging: active !== null,
      draftTargets: targets.draft,
      hostTargets: targets.host,
      activeTarget: accepted?.ok === true ? target : null,
    }
  }

  const frame = (): void => {
    if (disposed) return
    const proofHighlights: { hit: Hit; stroke: string; width: number; glow?: string | null }[] = []
    if (hostDiagram.regions[fixture.bubble] !== undefined) proofHighlights.push({ hit: { kind: 'region', id: fixture.bubble }, stroke: '#d97706', width: 2.7 })
    const presentation = externalPresentation()
    const connection = connectionDisplay()
    for (const wire of presentation.markedHost) proofHighlights.push({ hit: { kind: 'wire', id: wire }, stroke: '#2563eb', width: 2.2 })
    for (const wire of presentation.glowingHost) proofHighlights.push({ hit: { kind: 'wire', id: wire }, stroke: '#2563eb', width: 3.4, glow: '#2563eb' })
    for (const wire of connection.hostTargets) proofHighlights.push({ hit: { kind: 'wire', id: wire }, stroke: '#16a34a', width: 2.5 })
    if (connection.source?.kind === 'host') proofHighlights.push({ hit: { kind: 'wire', id: connection.source.wire }, stroke: '#16a34a', width: 2.8 })
    if (connection.activeTarget?.kind === 'host') proofHighlights.push({ hit: { kind: 'wire', id: connection.activeTarget.wire }, stroke: '#15803d', width: 3.8 })
    renderViewport(proofView, draft === null, proofHighlights)
    if (draft !== null) {
      const editorHighlights: { hit: Hit; stroke: string; width: number; glow?: string | null }[] = []
      for (const wire of presentation.markedDraft) editorHighlights.push({ hit: { kind: 'wire', id: wire }, stroke: '#2563eb', width: 2.2 })
      for (const wire of presentation.glowingDraft) editorHighlights.push({ hit: { kind: 'wire', id: wire }, stroke: '#2563eb', width: 3.4, glow: '#2563eb' })
      editorHighlights.push(...selectedDraft.map((hit) => ({ hit, stroke: '#d97706', width: 2.6 })))
      for (const wire of connection.draftTargets) editorHighlights.push({ hit: { kind: 'wire', id: wire }, stroke: '#16a34a', width: 2.3 })
      if (connection.source?.kind === 'draft') editorHighlights.push({ hit: { kind: 'wire', id: connection.source.wire }, stroke: '#16a34a', width: 2.8 })
      if (connection.activeTarget?.kind === 'draft') editorHighlights.push({ hit: { kind: 'wire', id: connection.activeTarget.wire }, stroke: '#15803d', width: 3.8 })
      // A connection hover/gesture captures the geometry that supplied its
      // visible target. The shared physics boundary deliberately overrides
      // this pause whenever the pointer phase is a Ctrl physics drag.
      const connectionGeometryCaptured = connection.source !== null || pointerGesture?.kind === 'slash'
      const advanceEditor = !connectionGeometryCaptured
      renderViewport(editorView, advanceEditor, editorHighlights, connection.source !== null ? '#16a34a' : '#2563eb')
    }
    editorCanvas.classList.toggle('is-connectable', connection.source !== null)
    proofCanvas.classList.toggle('is-connectable', connection.source !== null)
    gestureSvg.replaceChildren()
    if (connection.dragging && pointerGesture?.kind === 'connection') {
      gestureSvg.append(svgLine(pointerGesture.startClient, pointerGesture.currentClient, 'comp-join-gesture'))
    }
    if (pointerGesture?.kind === 'slash') {
      gestureSvg.append(svgLine(pointerGesture.startClient, pointerGesture.currentClient, 'comp-slash-gesture'))
    }
    raf = requestAnimationFrame(frame)
  }
  raf = requestAnimationFrame(frame)

  if (new URLSearchParams(location.search).has('debug')) {
    ;(window as any).__comprehensionDebug = {
      state: () => ({
        open: draft !== null,
        hostBubbleExists: hostDiagram.regions[fixture.bubble] !== undefined,
        hostSameAsStart: hostDiagram === fixture.diagram,
        boundary: draft === null ? [] : [...materializeComprehensionSnapshot(currentComprehensionDraft(draft)).relation.boundary],
        formalBoundary: draft === null ? [] : [...currentComprehensionDraft(draft).relation.boundary],
        externalWires: draft === null ? [] : [...currentComprehensionDraft(draft).externalWires],
        editor: editor.hidden ? null : { left: editor.offsetLeft, top: editor.offsetTop, width: editor.offsetWidth, height: editor.offsetHeight },
        editorHover: editorView.hover,
        proofSelected: proofView.selected,
        referencePreview: (() => {
          const connection = connectionDisplay()
          return connection.source === null || (connection.hostTargets.size === 0 && connection.draftTargets.size === 0)
            ? null
            : {
                source: connection.source,
                draftTargets: [...connection.draftTargets],
                hostTargets: [...connection.hostTargets],
                dragging: connection.dragging,
                activeTarget: connection.activeTarget,
              }
        })(),
        externalPresentation: (() => {
          const value = externalPresentation()
          return {
            markedDraft: [...value.markedDraft],
            markedHost: [...value.markedHost],
            glowingDraft: [...value.glowingDraft],
            glowingHost: [...value.glowingHost],
          }
        })(),
      }),
      open: () => openEditor(),
      addConstant: () => mutate((value) => addComprehensionTerm(value, parseTerm('a')), 'added'),
      graft: (draftWire: WireId, hostWire: WireId) => mutate((value) => applyComprehensionConnection(
        value,
        { kind: 'draft', wire: draftWire },
        { kind: 'host', wire: hostWire },
      ), 'grafted'),
      cancel: () => cancel.click(),
      commit: () => instantiate.click(),
      fixture: { ...fixture },
      draftWires: () => draft === null ? [] : Object.keys(currentComprehensionDraft(draft).relation.diagram.wires).map((wire) => ({ wire, point: wireClientPoint(editorView, wire, { x: innerWidth / 2, y: innerHeight / 2 }) })),
      hostWires: () => Object.keys(hostDiagram.wires).map((wire) => ({ wire, point: wireClientPoint(proofView, wire, { x: innerWidth / 2, y: innerHeight / 2 }) })),
    }
  }

  return {
    dispose(): void {
      disposed = true
      cancelAnimationFrame(raf)
      window.removeEventListener('keydown', onKey)
      if ((window as any).__comprehensionDebug !== undefined) delete (window as any).__comprehensionDebug
    },
  }
}
