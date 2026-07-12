import type { Diagram } from '../../kernel/diagram/diagram'
import { fitCamera, MIN_USER_ZOOM, normalizeUserZoom } from '../../view/camera'
import type { Engine } from '../../view/engine'
import { subtreeCarriers } from '../../view/engine'
import {
  advanceInteractivePhysics,
  cancelPhysicsDrag,
  commitPhysicsDragSample,
  type ActivePhysicsDrag,
  type PhysicsDrag,
} from '../../view/physics-drag'
import { length, sub, type Vec2 } from '../../view/vec'
import { brushHitTest, dragTarget, hitTest, type Hit } from '../hittest'
import {
  choosePointerPhase,
  createBrushState,
  reduceBrush,
  type BrushState,
  type PointerPhase,
} from './brush'

export type MutableView = { scale: number; offsetX: number; offsetY: number }

export type PointerSample = {
  readonly pointerId: number
  readonly button: number
  readonly client: Vec2
  readonly screen: Vec2
  readonly world: Vec2
  readonly hit: Hit | null
  readonly shiftKey: boolean
  readonly ctrlKey: boolean
  readonly altKey: boolean
  readonly metaKey: boolean
}

export type PointerClaim = {
  /** A still release either belongs to the claim (spawn/pending target) or is
      committed by the viewport as the ordinary selection toggle. */
  readonly still: 'claim' | 'selection'
  readonly blocksPassiveRelaxation: boolean
  /** Bodies held by a policy gesture. They are excluded from settling while
      every unheld degree of freedom continues through the shared solver. */
  readonly relaxationPins?: () => readonly string[]
  readonly move: (sample: PointerSample) => void
  readonly release: (sample: PointerSample, moved: boolean) => void
  readonly cancel: () => void
}

export type KeySample = {
  readonly key: string
  readonly shiftKey: boolean
  readonly ctrlKey: boolean
  readonly altKey: boolean
  readonly metaKey: boolean
  readonly repeat: boolean
}

export type InteractiveViewportOptions = {
  readonly canvas: HTMLCanvasElement
  readonly view: MutableView
  readonly engine: () => Engine
  readonly diagram: () => Diagram
  readonly selectionEnabled: () => boolean
  readonly claim: (sample: PointerSample) => PointerClaim | null
  readonly doubleClick: (sample: PointerSample) => boolean
  readonly contextMenu: (sample: PointerSample) => void
  readonly pointerChanged: (client: Vec2) => void
  readonly passiveSample?: (sample: PointerSample) => void
  readonly modifiersChanged?: (ctrlHeld: boolean) => void
  readonly keyDown: (sample: KeySample) => boolean
  readonly selectionChanged: (selected: readonly Hit[]) => void
  readonly selectionCommitted: () => void
  readonly inputAllowed?: () => boolean
}

const CLICK_SLOP_PX = 3
const ZOOM_PER_WHEEL_PX = 0.001

type ActivePointer = {
  readonly id: number
  readonly phase: PointerPhase
  readonly downClient: Vec2
  readonly downWorld: Vec2
  readonly initialSelection: readonly Hit[]
  readonly claim: PointerClaim | null
  brush: BrushState | null
  physics: { readonly drag: PhysicsDrag; readonly pinNode: string | null } | null
  activeDrag: ActivePhysicsDrag | null
  moved: boolean
  pinOnRelease: boolean
  releasedPins: string[]
}

function sameSelection(a: readonly Hit[], b: readonly Hit[]): boolean {
  return a.length === b.length && a.every((hit, i) => {
    const other = b[i]
    return other !== undefined && hit.kind === other.kind && hit.id === other.id
  })
}

/**
 * The sole owner of production canvas interaction. It converts coordinates,
 * captures exactly one pointer, arbitrates gesture phases, owns brush/pin/zoom
 * state, and commits every physics sample before animation-frame relaxation.
 */
export class InteractiveViewport {
  readonly #opts: InteractiveViewportOptions
  readonly #pins = new Set<string>()
  #selected: readonly Hit[] = []
  #hover: Hit | null = null
  #pointer: ActivePointer | null = null
  #userZoom = MIN_USER_ZOOM
  #cameraFocus: Vec2 | null = null

  constructor(opts: InteractiveViewportOptions) {
    this.#opts = opts
    const { canvas } = opts
    if (canvas.tabIndex < 0) canvas.tabIndex = 0
    canvas.addEventListener('pointerdown', this.#pointerDown)
    canvas.addEventListener('pointermove', this.#pointerMove)
    canvas.addEventListener('pointerup', this.#pointerUp)
    canvas.addEventListener('pointercancel', this.#pointerCancel)
    canvas.addEventListener('lostpointercapture', this.#lostPointerCapture)
    canvas.addEventListener('pointerleave', this.#pointerLeave)
    canvas.addEventListener('contextmenu', this.#contextMenu)
    canvas.addEventListener('dblclick', this.#doubleClick)
    canvas.addEventListener('wheel', this.#wheel, { passive: false })
    window.addEventListener('keydown', this.#keyDown)
    window.addEventListener('keyup', this.#modifierChanged)
  }

  get selection(): readonly Hit[] { return this.#selected }
  get hover(): Hit | null { return this.#hover }
  get pins(): ReadonlySet<string> { return this.#pins }
  get userZoom(): number { return this.#userZoom }

  get pinPreviewId(): string | null {
    const pointer = this.#pointer
    if (pointer === null || !pointer.pinOnRelease) return null
    return pointer.physics?.pinNode ?? null
  }

  setSelection(selected: readonly Hit[]): void {
    const next = createBrushState(selected).selected
    if (sameSelection(this.#selected, next)) return
    this.#selected = next
    this.#opts.selectionChanged(next)
  }

  cancelActiveGesture(): void {
    this.#cancelPointer(true)
  }

  /** Reconcile a new diagram on the same surface. Surviving node pins and the
      user's camera focus remain authoritative; selection is operation-local. */
  reconcileDiagram(preserveSelection = false): void {
    this.cancelActiveGesture()
    const diagram = this.#opts.diagram()
    const engine = this.#opts.engine()
    for (const id of this.#pins) {
      if (diagram.nodes[id] === undefined || !engine.bodies.has(id)) this.#pins.delete(id)
    }
    this.#hover = null
    this.setSelection(preserveSelection ? this.#selected.filter((hit) =>
      hit.kind === 'node' ? diagram.nodes[hit.id] !== undefined
        : hit.kind === 'region' ? diagram.regions[hit.id] !== undefined
          : diagram.wires[hit.id] !== undefined) : [])
    this.fit()
  }

  /** Enter a different proof/edit surface. Pins and focus belong to the old
      surface, while zoom magnitude remains a user viewport preference. */
  resetSurface(): void {
    this.cancelActiveGesture()
    this.#pins.clear()
    this.#hover = null
    this.#cameraFocus = null
    this.setSelection([])
    this.fit()
  }

  resetZoom(): void {
    this.#userZoom = MIN_USER_ZOOM
    this.#cameraFocus = null
    this.fit()
  }

  fit(): void {
    const engine = this.#opts.engine()
    const frame = engine.frame === null ? undefined : {
      center: engine.frame.center,
      radius: engine.frame.half,
    }
    const fitted = fitCamera(frame, this.#opts.canvas.width, this.#opts.canvas.height, this.#userZoom)
    const focus = this.#cameraFocus
    this.#opts.view.scale = fitted.scale
    this.#opts.view.offsetX = focus === null
      ? fitted.offsetX
      : this.#opts.canvas.width / 2 - focus.x * fitted.scale
    this.#opts.view.offsetY = focus === null
      ? fitted.offsetY
      : this.#opts.canvas.height / 2 - focus.y * fitted.scale
  }

  advance(allowPassiveRelaxation = true): void {
    const pins = new Set(this.#pins)
    for (const id of this.#pointer?.claim?.relaxationPins?.() ?? []) pins.add(id)
    advanceInteractivePhysics(
      this.#opts.engine(),
      pins,
      this.#pointer?.activeDrag ?? null,
      allowPassiveRelaxation && !(this.#pointer?.claim?.blocksPassiveRelaxation ?? false),
    )
    this.fit()
  }

  dispose(): void {
    this.cancelActiveGesture()
    const { canvas } = this.#opts
    canvas.removeEventListener('pointerdown', this.#pointerDown)
    canvas.removeEventListener('pointermove', this.#pointerMove)
    canvas.removeEventListener('pointerup', this.#pointerUp)
    canvas.removeEventListener('pointercancel', this.#pointerCancel)
    canvas.removeEventListener('lostpointercapture', this.#lostPointerCapture)
    canvas.removeEventListener('pointerleave', this.#pointerLeave)
    canvas.removeEventListener('contextmenu', this.#contextMenu)
    canvas.removeEventListener('dblclick', this.#doubleClick)
    canvas.removeEventListener('wheel', this.#wheel)
    window.removeEventListener('keydown', this.#keyDown)
    window.removeEventListener('keyup', this.#modifierChanged)
  }

  #screen(event: MouseEvent | WheelEvent): Vec2 {
    const rect = this.#opts.canvas.getBoundingClientRect()
    const sx = rect.width > 0 ? this.#opts.canvas.width / rect.width : 1
    const sy = rect.height > 0 ? this.#opts.canvas.height / rect.height : 1
    return { x: (event.clientX - rect.left) * sx, y: (event.clientY - rect.top) * sy }
  }

  #client(event: MouseEvent): Vec2 {
    return { x: event.clientX, y: event.clientY }
  }

  #sample(event: PointerEvent | MouseEvent): PointerSample {
    const screen = this.#screen(event)
    const world = this.#world(screen)
    const client = this.#client(event)
    this.#opts.pointerChanged(client)
    const sample: PointerSample = {
      pointerId: event instanceof PointerEvent ? event.pointerId : 1,
      button: event.button,
      client,
      screen,
      world,
      hit: hitTest(this.#opts.engine(), world, { scale: this.#opts.view.scale }),
      shiftKey: event.shiftKey,
      ctrlKey: event.ctrlKey,
      altKey: event.altKey,
      metaKey: event.metaKey,
    }
    this.#opts.passiveSample?.(sample)
    return sample
  }

  #world(screen: Vec2): Vec2 {
    const { view } = this.#opts
    return {
      x: (screen.x - view.offsetX) / view.scale,
      y: (screen.y - view.offsetY) / view.scale,
    }
  }

  #hit(world: Vec2, moving: boolean): Hit | null {
    return brushHitTest(this.#opts.engine(), world, { scale: this.#opts.view.scale }, moving)
  }

  #setBrush(next: BrushState): void {
    const pointer = this.#pointer
    if (pointer !== null) pointer.brush = next
    this.setSelection(next.selected)
  }

  #makePhysicsGrab(world: Vec2): { readonly drag: PhysicsDrag; readonly pinNode: string | null } | null {
    const engine = this.#opts.engine()
    const target = dragTarget(engine, world, { scale: this.#opts.view.scale })
    if (target === null) return null
    const ids = target.kind === 'body' ? [target.id] : subtreeCarriers(engine, target.id)
    const bodies = new Map<string, Vec2>()
    const origins = new Map<string, Vec2>()
    for (const id of ids) {
      const body = engine.bodies.get(id)
      if (body !== undefined) {
        bodies.set(id, sub(body.pos, world))
        origins.set(id, { ...body.pos })
      }
    }
    if (bodies.size === 0) return null
    const pinNode = target.kind === 'body' && this.#opts.diagram().nodes[target.id] !== undefined
      ? target.id
      : null
    return { drag: { bodies, origins }, pinNode }
  }

  #pointerDown = (event: PointerEvent): void => {
    if (this.#opts.inputAllowed?.() === false) { event.preventDefault(); return }
    if ((event.button !== 0 && event.button !== 2) || this.#pointer !== null) return
    this.#opts.canvas.focus({ preventScroll: true })
    const sample = this.#sample(event)
    const claim = this.#opts.claim(sample)
    const phase = event.button === 2
      ? (!event.shiftKey && !event.ctrlKey && claim !== null ? 'claimed' : null)
      : this.#opts.selectionEnabled()
        ? choosePointerPhase(event, claim !== null)
        : event.shiftKey ? 'claimed' : event.ctrlKey ? 'physics' : 'claimed'
    if (phase === null) return
    const brush = phase === 'selection'
      ? reduceBrush(createBrushState(this.#selected), { kind: 'begin', hit: sample.hit })
      : null
    this.#pointer = {
      id: event.pointerId,
      phase,
      downClient: sample.client,
      downWorld: sample.world,
      initialSelection: this.#selected,
      claim,
      brush,
      physics: phase === 'physics' ? this.#makePhysicsGrab(sample.world) : null,
      activeDrag: null,
      moved: false,
      pinOnRelease: false,
      releasedPins: [],
    }
    this.#hover = sample.hit
    if (brush !== null) this.#setBrush(brush)
    this.#opts.canvas.setPointerCapture(event.pointerId)
    event.preventDefault()
  }

  #pointerMove = (event: PointerEvent): void => {
    if (this.#opts.inputAllowed?.() === false) return
    const sample = this.#sample(event)
    const pointer = this.#pointer
    if (pointer === null || pointer.id !== event.pointerId) {
      this.#hover = sample.hit
      return
    }
    if (length(sub(sample.client, pointer.downClient)) > CLICK_SLOP_PX) this.#engageMove(pointer)
    this.#hover = this.#hit(sample.world, pointer.moved)
    if (!pointer.moved) return

    if (pointer.phase === 'selection' && pointer.brush !== null) {
      this.#setBrush(reduceBrush(pointer.brush, { kind: 'move', hit: this.#hit(sample.world, true) }))
    } else if (pointer.phase === 'physics' && pointer.physics !== null) {
      pointer.activeDrag = { drag: pointer.physics.drag, cursor: sample.world }
      pointer.pinOnRelease = pointer.physics.pinNode !== null && !event.ctrlKey
      commitPhysicsDragSample(this.#opts.engine(), pointer.activeDrag)
    } else if (pointer.phase === 'claimed') {
      pointer.claim?.move(sample)
    }
    event.preventDefault()
  }

  #pointerUp = (event: PointerEvent): void => {
    const pointer = this.#pointer
    if (pointer === null || pointer.id !== event.pointerId) return
    const sample = this.#sample(event)
    if (length(sub(sample.client, pointer.downClient)) > CLICK_SLOP_PX) this.#engageMove(pointer)
    this.#hover = this.#hit(sample.world, pointer.moved)
    if (pointer.phase === 'selection' && pointer.brush !== null) {
      const sampled = pointer.moved
        ? reduceBrush(pointer.brush, { kind: 'move', hit: this.#hit(sample.world, true) })
        : pointer.brush
      this.#setBrush(reduceBrush(sampled, { kind: 'end' }))
      if (!sameSelection(pointer.initialSelection, this.#selected)) this.#opts.selectionCommitted()
    } else if (pointer.phase === 'claimed' && pointer.claim !== null) {
      if (pointer.moved) pointer.claim.move(sample)
      pointer.claim.release(sample, pointer.moved)
      if (!pointer.moved && pointer.claim.still === 'selection') this.#commitStillSelection(sample.hit)
    } else if (pointer.phase === 'physics' && pointer.physics !== null && pointer.moved) {
      pointer.activeDrag = { drag: pointer.physics.drag, cursor: sample.world }
      commitPhysicsDragSample(this.#opts.engine(), pointer.activeDrag)
      const wantsPin = !event.ctrlKey
      if (wantsPin && pointer.physics.pinNode !== null) {
        const id = pointer.physics.pinNode
        this.#pins.add(id)
      }
    }
    this.#finishCommittedPointer(true)
    event.preventDefault()
  }

  #pointerCancel = (event: PointerEvent): void => {
    if (this.#pointer?.id !== event.pointerId) return
    this.#cancelPointer(true)
  }

  #lostPointerCapture = (event: PointerEvent): void => {
    if (this.#pointer?.id !== event.pointerId) return
    this.#cancelPointer(false)
  }

  #pointerLeave = (): void => {
    this.#hover = null
  }

  #contextMenu = (event: MouseEvent): void => {
    event.preventDefault()
    if (this.#opts.inputAllowed?.() === false) return
    this.#opts.contextMenu(this.#sample(event))
  }

  #doubleClick = (event: MouseEvent): void => {
    if (this.#opts.inputAllowed?.() === false) { event.preventDefault(); return }
    if (this.#opts.doubleClick(this.#sample(event))) event.preventDefault()
  }

  #commitStillSelection(hit: Hit | null): void {
    const initial = this.#selected
    const begun = reduceBrush(createBrushState(initial), { kind: 'begin', hit })
    const ended = reduceBrush(begun, { kind: 'end' })
    this.setSelection(ended.selected)
    if (!sameSelection(initial, this.#selected)) this.#opts.selectionCommitted()
  }

  #engageMove(pointer: ActivePointer): void {
    if (pointer.moved) return
    pointer.moved = true
    if (pointer.phase === 'selection') {
      const movingStart = reduceBrush(
        createBrushState(pointer.initialSelection),
        { kind: 'begin', hit: this.#hit(pointer.downWorld, true) },
      )
      this.#setBrush(movingStart)
    } else if (pointer.phase === 'physics' && pointer.physics !== null) {
      for (const id of pointer.physics.drag.bodies.keys()) {
        if (this.#pins.delete(id)) pointer.releasedPins.push(id)
      }
    }
  }

  #finishCommittedPointer(releaseCapture: boolean): void {
    const pointer = this.#pointer
    if (pointer === null) return
    this.#pointer = null
    if (releaseCapture && this.#opts.canvas.hasPointerCapture(pointer.id)) {
      this.#opts.canvas.releasePointerCapture(pointer.id)
    }
  }

  #cancelPointer(releaseCapture: boolean): void {
    const pointer = this.#pointer
    if (pointer === null) return
    if (pointer.phase === 'selection') this.setSelection(pointer.initialSelection)
    if (pointer.phase === 'physics' && pointer.physics !== null && pointer.moved) {
      cancelPhysicsDrag(this.#opts.engine(), pointer.physics.drag)
      for (const id of pointer.releasedPins) this.#pins.add(id)
    }
    if (pointer.phase === 'claimed') pointer.claim?.cancel()
    this.#finishCommittedPointer(releaseCapture)
  }

  #modifierChanged = (event: KeyboardEvent): void => {
    if (event.key !== 'Control') return
    this.#opts.modifiersChanged?.(event.ctrlKey)
    const pointer = this.#pointer
    if (pointer === null || pointer.phase !== 'physics' || !pointer.moved) return
    pointer.pinOnRelease = event.type === 'keyup'
      && pointer.physics !== null
      && pointer.physics.pinNode !== null
  }

  #keyDown = (event: KeyboardEvent): void => {
    this.#modifierChanged(event)
    const target = event.target
    if (target instanceof HTMLInputElement || target instanceof HTMLTextAreaElement || (target instanceof HTMLElement && target.isContentEditable)) return
    if (this.#opts.inputAllowed?.() === false) { event.preventDefault(); return }
    const consumed = this.#opts.keyDown({
      key: event.key,
      shiftKey: event.shiftKey,
      ctrlKey: event.ctrlKey,
      altKey: event.altKey,
      metaKey: event.metaKey,
      repeat: event.repeat,
    })
    if (consumed) event.preventDefault()
  }

  #wheel = (event: WheelEvent): void => {
    event.preventDefault()
    if (this.#opts.inputAllowed?.() === false) return
    const screen = this.#screen(event)
    const world = this.#world(screen)
    const delta = event.deltaMode === WheelEvent.DOM_DELTA_LINE
      ? event.deltaY * 16
      : event.deltaMode === WheelEvent.DOM_DELTA_PAGE
        ? event.deltaY * this.#opts.canvas.height
        : event.deltaY
    this.#userZoom = normalizeUserZoom(this.#userZoom * Math.exp(-delta * ZOOM_PER_WHEEL_PX))
    if (this.#userZoom === MIN_USER_ZOOM) {
      this.#cameraFocus = null
      this.fit()
      return
    }
    const engine = this.#opts.engine()
    const frame = engine.frame === null ? undefined : {
      center: engine.frame.center,
      radius: engine.frame.half,
    }
    const scale = fitCamera(frame, this.#opts.canvas.width, this.#opts.canvas.height, this.#userZoom).scale
    this.#cameraFocus = {
      x: world.x - (screen.x - this.#opts.canvas.width / 2) / scale,
      y: world.y - (screen.y - this.#opts.canvas.height / 2) / scale,
    }
    this.fit()
  }
}
