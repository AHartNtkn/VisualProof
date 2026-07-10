import type { Diagram } from '../kernel/diagram/diagram'
import { occurrenceSelection, findOccurrences } from '../kernel/diagram/subgraph/match'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { checkTheorem } from '../kernel/proof/theorem'
import { verifyTheory } from '../kernel/proof/store'
import { buildFregeTheory } from '../theories/frege'
import type { Vec2 } from '../view/vec'
import { length, sub } from '../view/vec'
import type { Engine } from '../view/engine'
import { carryOver, mkEngine, subtreeCarriers } from '../view/engine'
import { seedProject, settleStep } from '../view/relax'
import type { DragProjection } from '../view/constraints'
import { commitBodyPositions, projectDragToSemanticFrontier } from '../view/constraints'
import { fitCamera, MIN_USER_ZOOM, normalizeUserZoom } from '../view/camera'
import type { Shape } from '../view/paint'
import { LIGHT, paint } from '../view/paint'
import { adaptCanvas, type CanvasAdapter } from '../view/canvas'
import { existentialStubs, legPaths } from '../view/wires'
import type { Hit } from './hittest'
import { dragTarget, hitTest } from './hittest'
import type { ProofSession, Side } from './session'
import { applyBackward, applyForward, assembleTheorem, meet, sideBoundary, startSession } from './session'

type FrontId = 'forward' | 'backward'

const CLICK_SLOP_PX = 3
const ZOOM_PER_WHEEL_PX = 0.001
const FUEL = 64

type Drag = { readonly bodies: ReadonlyMap<string, Vec2> }

type Front = {
  readonly id: FrontId
  readonly pane: HTMLElement
  readonly canvas: HTMLCanvasElement
  readonly surface: CanvasAdapter
  readonly label: HTMLElement
  readonly status: HTMLElement
  citeButton: HTMLButtonElement
  undoButton: HTMLButtonElement
  redoButton: HTMLButtonElement
  fitButton: HTMLButtonElement
  readonly scrubber: HTMLInputElement
  engine: Engine
  diagram: Diagram
  view: { scale: number; offsetX: number; offsetY: number }
  userZoom: number
  cameraFocus: Vec2 | null
  selected: Hit | null
  hover: Hit | null
  pins: Set<string>
  downScreen: Vec2 | null
  drag: Drag | null
  dragMoved: boolean
  activeDrag: { readonly drag: Drag; readonly screen: Vec2 } | null
  pinOnRelease: boolean
  suspendedPins: string[]
  projection: DragProjection | null
  history: Side[]
  cursor: number
  message: string
}

export type DualFrontPrototype = {
  dispose(): void
}

function button(label: string, action: () => void): HTMLButtonElement {
  const b = document.createElement('button')
  b.type = 'button'
  b.textContent = label
  b.addEventListener('click', (event) => {
    event.stopPropagation()
    action()
  })
  return b
}

function frontMarkup(id: FrontId): {
  pane: HTMLElement
  canvas: HTMLCanvasElement
  label: HTMLElement
  status: HTMLElement
  controls: HTMLElement
  scrubber: HTMLInputElement
} {
  const pane = document.createElement('section')
  pane.className = `dual-front-pane dual-front-${id}`
  pane.dataset.front = id

  const header = document.createElement('header')
  header.className = 'dual-front-header'
  const label = document.createElement('strong')
  label.className = 'dual-front-label'
  label.textContent = id
  const status = document.createElement('span')
  status.className = 'dual-front-status'
  const controls = document.createElement('span')
  controls.className = 'dual-front-controls'
  header.append(label, status, controls)

  const canvas = document.createElement('canvas')
  canvas.id = `${id}-canvas`
  canvas.className = 'dual-front-canvas'

  const history = document.createElement('footer')
  history.className = 'dual-front-history'
  const historyLabel = document.createElement('span')
  historyLabel.textContent = 'history'
  const scrubber = document.createElement('input')
  scrubber.type = 'range'
  scrubber.min = '0'
  scrubber.max = '0'
  scrubber.step = '1'
  scrubber.value = '0'
  scrubber.setAttribute('aria-label', `${id} history`)
  history.append(historyLabel, scrubber)

  pane.append(header, canvas, history)
  return { pane, canvas, label, status, controls, scrubber }
}

function localPoint(canvas: HTMLCanvasElement, event: PointerEvent | WheelEvent): Vec2 {
  const rect = canvas.getBoundingClientRect()
  return { x: event.clientX - rect.left, y: event.clientY - rect.top }
}

function worldPoint(front: Front, screen: Vec2): Vec2 {
  return {
    x: (screen.x - front.view.offsetX) / front.view.scale,
    y: (screen.y - front.view.offsetY) / front.view.scale,
  }
}

function markerAt(front: Front, id: string): Vec2 | null {
  const body = front.engine.bodies.get(id)
  if (body === undefined) return null
  const radius = body.discR * front.engine.scale
  return { x: body.pos.x + radius * 0.72, y: body.pos.y - radius * 0.72 }
}

function hitShapes(front: Front, hit: Hit, stroke: string, width: number): Shape[] {
  if (hit.kind === 'node') {
    const body = front.engine.bodies.get(hit.id)
    return body === undefined ? [] : [{
      kind: 'circle', center: body.pos, r: body.discR * front.engine.scale + 1,
      fill: null, stroke, width, insetColor: null, glow: null,
    }]
  }
  if (hit.kind === 'region') {
    const region = front.engine.regions.get(hit.id)
    return region === undefined ? [] : [{
      kind: 'circle', center: region.center, r: region.radius + 0.8,
      fill: null, stroke, width, insetColor: null, glow: null,
    }]
  }
  const out: Shape[] = []
  for (const leg of legPaths(front.engine)) {
    if (leg.wid === hit.id) out.push({ kind: 'polyline', pts: leg.pts, stroke, width, glow: null })
  }
  for (const stub of existentialStubs(front.engine)) {
    if (stub.wid === hit.id) out.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width, glow: null })
  }
  return out
}

function fitFront(front: Front): void {
  const frame = front.engine.frame
  const { width, height } = front.surface.size()
  const camera = fitCamera(frame === null ? undefined : { center: frame.center, radius: frame.half }, width, height, front.userZoom)
  front.view.scale = camera.scale
  front.view.offsetX = camera.offsetX
  front.view.offsetY = camera.offsetY
  if (front.cameraFocus !== null) {
    front.view.offsetX = width / 2 - front.cameraFocus.x * front.view.scale
    front.view.offsetY = height / 2 - front.cameraFocus.y * front.view.scale
  }
}

function grabAt(front: Front, world: Vec2): Drag | null {
  const target = dragTarget(front.engine, world, { scale: front.view.scale })
  if (target === null) return null
  const ids = target.kind === 'body' ? [target.id] : subtreeCarriers(front.engine, target.id)
  const bodies = new Map<string, Vec2>()
  for (const id of ids) {
    const body = front.engine.bodies.get(id)
    if (body !== undefined) bodies.set(id, { x: body.pos.x - world.x, y: body.pos.y - world.y })
  }
  return bodies.size === 0 ? null : { bodies }
}

function pinEligible(front: Front, drag: Drag | null): drag is Drag {
  if (drag === null || drag.bodies.size !== 1) return false
  const id = drag.bodies.keys().next().value as string | undefined
  return id !== undefined && front.diagram.nodes[id] !== undefined
}

function sideOf(session: ProofSession, id: FrontId): Side {
  return id === 'forward' ? session.forward : session.backward
}

export function mountDualFrontPrototype(host: HTMLElement): DualFrontPrototype {
  const ctx: ProofContext = verifyTheory(buildFregeTheory())
  const goal = ctx.theorems.get('succNat')
  if (goal === undefined) throw new Error("the dual-front fixture requires the verified 'succNat' theorem")
  let session = startSession(goal.lhs, goal.rhs, ctx)
  let focused: FrontId = 'forward'
  let declared: string | null = null
  let ratio = 0.5
  let disposed = false
  let raf = 0

  host.replaceChildren()
  host.className = 'dual-front-root'
  const forwardDom = frontMarkup('forward')
  const backwardDom = frontMarkup('backward')
  const seam = document.createElement('div')
  seam.className = 'dual-front-seam'
  seam.title = 'drag to allocate space; double-click to equalize'
  const meetButton = document.createElement('button')
  meetButton.type = 'button'
  meetButton.className = 'dual-front-meet'
  seam.append(meetButton)
  host.append(forwardDom.pane, seam, backwardDom.pane)

  const makeFront = (id: FrontId, dom: typeof forwardDom): Front => {
    const surface = adaptCanvas(dom.canvas)
    const side = sideOf(session, id)
    const diagram = side.current
    const engine = mkEngine(diagram, sideBoundary(session, id))
    seedProject(engine)
    const front: Front = {
      id,
      pane: dom.pane,
      canvas: dom.canvas,
      surface,
      label: dom.label,
      status: dom.status,
      citeButton: document.createElement('button'),
      undoButton: document.createElement('button'),
      redoButton: document.createElement('button'),
      fitButton: document.createElement('button'),
      scrubber: dom.scrubber,
      engine,
      diagram,
      view: { scale: 1, offsetX: 0, offsetY: 0 },
      userZoom: 1,
      cameraFocus: null,
      selected: null,
      hover: null,
      pins: new Set(),
      downScreen: null,
      drag: null,
      dragMoved: false,
      activeDrag: null,
      pinOnRelease: false,
      suspendedPins: [],
      projection: null,
      history: [side],
      cursor: 0,
      message: 'Ctrl-drag; release Ctrl before pointer-up to pin · wheel zooms here',
    }
    front.citeButton = button('Apply succNat', () => applyCitation(id))
    front.undoButton = button('Undo', () => moveHistory(id, -1))
    front.redoButton = button('Redo', () => moveHistory(id, 1))
    front.fitButton = button('Fit', () => {
      front.userZoom = 1
      front.cameraFocus = null
      front.message = 'camera fit to the full boundary'
      updateChrome()
    })
    dom.controls.append(front.citeButton, front.undoButton, front.redoButton, front.fitButton)
    return front
  }

  let fronts = {} as Record<FrontId, Front>
  const forward = makeFront('forward', forwardDom)
  const backward = makeFront('backward', backwardDom)
  fronts = { forward, backward }

  const setSessionSide = (id: FrontId, side: Side): void => {
    session = id === 'forward' ? { ...session, forward: side } : { ...session, backward: side }
  }

  const syncDiagram = (front: Front): void => {
    const diagram = sideOf(session, front.id).current
    if (diagram === front.diagram) return
    const next = mkEngine(diagram, sideBoundary(session, front.id))
    carryOver(front.engine, next)
    seedProject(next)
    front.engine = next
    front.diagram = diagram
    front.selected = null
    front.hover = null
    front.activeDrag = null
    front.projection = null
    for (const id of [...front.pins]) if (diagram.nodes[id] === undefined) front.pins.delete(id)
  }

  const updateChrome = (): void => {
    const met = meet(session)
    for (const id of ['forward', 'backward'] as const) {
      const front = fronts[id]
      front.pane.classList.toggle('is-focused', focused === id)
      front.label.textContent = id === 'forward' ? 'FORWARD FRONT' : 'BACKWARD FRONT'
      front.status.textContent = `${front.cursor}/${front.history.length - 1} · ${front.pins.size} ${front.pins.size === 1 ? 'pin' : 'pins'} · ${front.message}`
      front.scrubber.max = String(front.history.length - 1)
      front.scrubber.value = String(front.cursor)
      front.undoButton.disabled = front.cursor === 0
      front.redoButton.disabled = front.cursor === front.history.length - 1
    }
    seam.classList.toggle('is-met', met)
    seam.classList.toggle('is-declared', declared !== null)
    meetButton.disabled = !met
    meetButton.textContent = declared !== null ? `DECLARED · ${declared}` : met ? 'MEET · DECLARE' : 'DISTINCT'
  }

  const setFocus = (id: FrontId): void => {
    focused = id
    updateChrome()
  }

  const citationStep = (id: FrontId): ProofStep => {
    const direction = id === 'forward' ? 'forward' as const : 'reverse' as const
    const from = direction === 'forward' ? goal.lhs : goal.rhs
    const hostDiagram = sideOf(session, id).current
    const matches = [...findOccurrences(hostDiagram, from, { fuel: FUEL, mode: 'exact' }).matches]
    if (matches.length !== 1) throw new Error(`expected one '${goal.name}' occurrence on the ${id} front, found ${matches.length}`)
    const occurrence = matches[0]!
    return {
      rule: 'theorem',
      name: goal.name,
      direction,
      at: { sel: occurrenceSelection(from, occurrence, hostDiagram), args: [...occurrence.attachments] },
    }
  }

  const applyCitation = (id: FrontId): void => {
    const front = fronts[id]
    try {
      const step = citationStep(id)
      session = id === 'forward' ? applyForward(session, step) : applyBackward(session, step)
      const nextSide = sideOf(session, id)
      front.history = [...front.history.slice(0, front.cursor + 1), nextSide]
      front.cursor++
      declared = null
      front.message = `applied ${goal.name} ${id === 'forward' ? 'forward' : 'in backward orientation'}`
      syncDiagram(front)
    } catch (error) {
      front.message = error instanceof Error ? error.message : String(error)
    }
    updateChrome()
  }

  const moveHistory = (id: FrontId, delta: number): void => {
    const front = fronts[id]
    const next = Math.max(0, Math.min(front.history.length - 1, front.cursor + delta))
    if (next === front.cursor) {
      front.message = delta < 0 ? 'nothing to undo on this front' : 'nothing to redo on this front'
      updateChrome()
      return
    }
    front.cursor = next
    setSessionSide(id, front.history[next]!)
    declared = null
    front.message = next < front.history.length - 1 ? `viewing history state ${next}` : 'at the latest state'
    syncDiagram(front)
    updateChrome()
  }

  const declareMeet = (): void => {
    if (!meet(session)) return
    const proposed = window.prompt('Name the theorem formed by this meet', 'dualMeet')
    if (proposed === null) return
    const name = proposed.trim()
    if (name === '') {
      fronts[focused].message = 'a theorem name cannot be empty'
      updateChrome()
      return
    }
    try {
      const theorem = assembleTheorem(session, name)
      checkTheorem(theorem, ctx)
      declared = name
      fronts[focused].message = `theorem '${name}' replay-checked`
    } catch (error) {
      fronts[focused].message = error instanceof Error ? error.message : String(error)
    }
    updateChrome()
  }

  meetButton.addEventListener('click', declareMeet)

  for (const id of ['forward', 'backward'] as const) {
    const front = fronts[id]
    front.pane.addEventListener('pointerdown', () => setFocus(id))
    front.scrubber.addEventListener('input', () => {
      const next = Number(front.scrubber.value)
      const delta = next - front.cursor
      if (delta !== 0) moveHistory(id, delta)
    })

    front.canvas.addEventListener('pointerdown', (event) => {
      setFocus(id)
      const screen = localPoint(front.canvas, event)
      front.downScreen = screen
      front.dragMoved = false
      front.pinOnRelease = false
      front.suspendedPins = []
      front.projection = null
      front.drag = event.ctrlKey ? grabAt(front, worldPoint(front, screen)) : null
      front.canvas.setPointerCapture(event.pointerId)
    })

    front.canvas.addEventListener('pointermove', (event) => {
      const screen = localPoint(front.canvas, event)
      front.hover = hitTest(front.engine, worldPoint(front, screen), { scale: front.view.scale })
      if (front.downScreen === null || front.drag === null) return
      if (!front.dragMoved && length(sub(screen, front.downScreen)) > CLICK_SLOP_PX) {
        front.dragMoved = true
        for (const bodyId of front.drag.bodies.keys()) {
          if (front.pins.delete(bodyId)) front.suspendedPins.push(bodyId)
        }
      }
      if (!front.dragMoved) return
      front.pinOnRelease = pinEligible(front, front.drag) && !event.ctrlKey
      front.activeDrag = { drag: front.drag, screen }
    })

    front.canvas.addEventListener('pointerleave', () => { front.hover = null })

    front.canvas.addEventListener('pointerup', (event) => {
      const screen = localPoint(front.canvas, event)
      if (front.downScreen !== null && !front.dragMoved) {
        const hit = hitTest(front.engine, worldPoint(front, screen), { scale: front.view.scale })
        front.selected = hit !== null && front.selected?.kind === hit.kind && front.selected.id === hit.id ? null : hit
        front.message = hit === null ? 'selection cleared' : `selected ${hit.kind} '${hit.id}'`
      } else if (front.dragMoved && front.drag !== null && pinEligible(front, front.drag) && !event.ctrlKey) {
        const bodyId = front.drag.bodies.keys().next().value as string
        front.pins.add(bodyId)
        front.message = `pinned node '${bodyId}'`
      } else if (front.dragMoved && front.suspendedPins.length > 0) {
        front.message = `${front.suspendedPins.length === 1 ? `node '${front.suspendedPins[0]}'` : 'moved nodes'} left unpinned; unrelated pins remain`
      }
      front.downScreen = null
      front.drag = null
      front.dragMoved = false
      front.activeDrag = null
      front.pinOnRelease = false
      front.suspendedPins = []
      front.projection = null
      updateChrome()
    })

    front.canvas.addEventListener('wheel', (event) => {
      event.preventDefault()
      const screen = localPoint(front.canvas, event)
      const underCursor = worldPoint(front, screen)
      front.userZoom = normalizeUserZoom(front.userZoom * Math.exp(-event.deltaY * ZOOM_PER_WHEEL_PX))
      if (front.userZoom === MIN_USER_ZOOM) {
        front.cameraFocus = null
        fitFront(front)
        return
      }
      const frame = front.engine.frame
      const { width, height } = front.surface.size()
      const nextScale = fitCamera(frame === null ? undefined : { center: frame.center, radius: frame.half }, width, height, front.userZoom).scale
      front.cameraFocus = {
        x: underCursor.x - (screen.x - width / 2) / nextScale,
        y: underCursor.y - (screen.y - height / 2) / nextScale,
      }
      fitFront(front)
    }, { passive: false })
  }

  const updateLayout = (): void => {
    host.style.gridTemplateColumns = `minmax(0, ${ratio * 100}fr) 14px minmax(0, ${(1 - ratio) * 100}fr)`
  }

  let resizing = false
  seam.addEventListener('pointerdown', (event) => {
    if (event.target === meetButton) return
    resizing = true
    seam.setPointerCapture(event.pointerId)
    event.preventDefault()
  })
  seam.addEventListener('pointermove', (event) => {
    if (!resizing) return
    const rect = host.getBoundingClientRect()
    ratio = Math.max(0.3, Math.min(0.7, (event.clientX - rect.left) / rect.width))
    updateLayout()
  })
  seam.addEventListener('pointerup', () => { resizing = false })
  seam.addEventListener('dblclick', () => { ratio = 0.5; updateLayout() })
  updateLayout()

  const onKeyDown = (event: KeyboardEvent): void => {
    if (document.activeElement instanceof HTMLInputElement) return
    const front = fronts[focused]
    if ((event.ctrlKey || event.metaKey) && (event.key === 'z' || event.key === 'Z')) {
      event.preventDefault()
      moveHistory(focused, event.shiftKey ? 1 : -1)
    } else if (event.key === 'c' || event.key === 'C') {
      applyCitation(focused)
    } else if (event.key === 'Home') {
      front.userZoom = 1
      front.cameraFocus = null
      front.message = 'camera fit to the full boundary'
      updateChrome()
      event.preventDefault()
    } else if (event.key === 'd' || event.key === 'D') {
      declareMeet()
    }
  }
  window.addEventListener('keydown', onKeyDown)

  const frame = (): void => {
    if (disposed) return
    for (const id of ['forward', 'backward'] as const) {
      const front = fronts[id]
      if (!front.surface.syncSize()) continue
      const pinned = new Set(front.pins)
      if (front.activeDrag !== null) for (const bodyId of front.activeDrag.drag.bodies.keys()) pinned.add(bodyId)
      settleStep(front.engine, pinned.size === 0 ? null : pinned)
      if (front.activeDrag !== null) {
        const at = worldPoint(front, front.activeDrag.screen)
        const targets = new Map<string, Vec2>()
        for (const [bodyId, offset] of front.activeDrag.drag.bodies) {
          targets.set(bodyId, { x: at.x + offset.x, y: at.y + offset.y })
        }
        front.projection = projectDragToSemanticFrontier(front.engine, targets)
        commitBodyPositions(front.engine, front.projection.positions)
      } else {
        front.projection = null
      }
      fitFront(front)
      const shapes = paint(front.engine, LIGHT)
      for (const pinId of front.pins) {
        const body = front.engine.bodies.get(pinId)
        if (body === undefined) continue
        shapes.push({ kind: 'circle', center: body.pos, r: body.discR * front.engine.scale + 1.1, fill: null, stroke: '#dc2626', width: 1.5, insetColor: null, glow: null })
        const marker = markerAt(front, pinId)
        if (marker !== null) shapes.push({ kind: 'dot', center: marker, rPx: 5.5, fill: '#dc2626' })
      }
      if (front.activeDrag !== null && front.pinOnRelease) {
        const first = front.activeDrag.drag.bodies.keys().next().value as string | undefined
        const marker = first === undefined ? null : markerAt(front, first)
        if (marker !== null) shapes.push({ kind: 'dot', center: marker, rPx: 8, fill: '#dc2626' })
      }
      if (front.selected !== null) shapes.push(...hitShapes(front, front.selected, '#d97706', 2.5))
      if (front.hover !== null) shapes.push(...hitShapes(front, front.hover, '#2563eb', 1.8))
      front.surface.render(shapes, front.view)
    }
    raf = requestAnimationFrame(frame)
  }

  updateChrome()
  raf = requestAnimationFrame(frame)

  if (new URLSearchParams(location.search).has('debug')) {
    ;(window as any).__dualFrontDebug = {
      state: () => ({ focused, ratio, met: meet(session), declared }),
      front: (id: FrontId) => {
        const front = fronts[id]
        return {
          view: { ...front.view },
          zoom: front.userZoom,
          cameraFocus: front.cameraFocus === null ? null : { ...front.cameraFocus },
          pins: [...front.pins],
          selected: front.selected,
          cursor: front.cursor,
          history: front.history.length,
          blocked: front.projection?.blocked ?? false,
          frame: front.engine.frame === null ? null : { center: { ...front.engine.frame.center }, half: front.engine.frame.half },
          bodies: [...front.engine.bodies.values()].map((body) => ({ id: body.id, kind: body.kind, x: body.pos.x, y: body.pos.y, r: body.discR * front.engine.scale, region: body.region })),
          regions: [...front.engine.regions.entries()].map(([regionId, circle]) => {
            const region = front.diagram.regions[regionId]
            return { id: regionId, kind: region?.kind ?? '?', parent: region !== undefined && region.kind !== 'sheet' ? region.parent : null, x: circle.center.x, y: circle.center.y, r: circle.radius }
          }),
        }
      },
      focus: setFocus,
      cite: applyCitation,
      undo: (id: FrontId) => moveHistory(id, -1),
      redo: (id: FrontId) => moveHistory(id, 1),
      setRatio: (next: number) => { ratio = Math.max(0.3, Math.min(0.7, next)); updateLayout() },
    }
  }

  return {
    dispose(): void {
      disposed = true
      cancelAnimationFrame(raf)
      window.removeEventListener('keydown', onKeyDown)
      if ((window as any).__dualFrontDebug !== undefined) delete (window as any).__dualFrontDebug
    },
  }
}
