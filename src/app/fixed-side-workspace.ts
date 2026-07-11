import type { ProofContext, ProofStep } from '../kernel/proof/step'
import type { Theme } from '../view/paint'
import type { Vec2 } from '../view/vec'
import {
  applyBackward,
  applyForward,
  currentSide,
  meet,
  moveSide,
  sideBoundary,
  type ProofSession,
} from './session'
import {
  dividerRatioAt,
  FIXED_SIDE_SEAM_WIDTH,
  MIN_FIXED_WORKSPACE_WIDTH,
  paneGeometry,
  type FixedSide,
  type FixedSideGeometry,
} from './fixed-side-layout'
import { ProofFrontViewport, type ProofFrontDebugState } from './proof-front'
import type { KeySample } from './interact/viewport'

export type FixedSideWorkspaceOptions = {
  readonly host: HTMLElement
  session(): ProofSession
  commit(session: ProofSession, changedSide: FixedSide): void
  context(): ProofContext
  theme(): Theme
  fuel(): number
  focusChanged(side: FixedSide): void
  declare(): void
  refuse(text: string, pointer: Vec2): void
  changed(): void
}

export type FixedSideWorkspaceDebug = {
  readonly ratio: number
  readonly focused: FixedSide
  readonly met: boolean
  readonly forward: ProofFrontDebugState & { readonly cursor: number; readonly selected: number; readonly pinCount: number }
  readonly backward: ProofFrontDebugState & { readonly cursor: number; readonly selected: number; readonly pinCount: number }
}

export class FixedSideWorkspace {
  readonly root: HTMLDivElement
  readonly seam: HTMLDivElement
  readonly forward: ProofFrontViewport
  readonly backward: ProofFrontViewport
  #options: FixedSideWorkspaceOptions
  #focused: FixedSide = 'forward'
  #ratio = 0.5
  #geometry: FixedSideGeometry
  #dragging = false
  #disposed = false
  #forwardPane: HTMLDivElement
  #backwardPane: HTMLDivElement
  #forwardStatus: HTMLOutputElement
  #backwardStatus: HTMLOutputElement
  #declareButton: HTMLButtonElement
  #narrowNotice: HTMLDivElement

  constructor(options: FixedSideWorkspaceOptions) {
    if (window.innerWidth < MIN_FIXED_WORKSPACE_WIDTH) {
      throw new Error(`fixed-side proving requires a window at least ${MIN_FIXED_WORKSPACE_WIDTH}px wide`)
    }
    this.#options = options
    this.root = document.createElement('div')
    this.root.className = 'vpa-fixed-side-workspace'
    const forwardDom = this.#makePane('forward')
    const backwardDom = this.#makePane('backward')
    this.#forwardPane = forwardDom.pane
    this.#backwardPane = backwardDom.pane
    this.#forwardStatus = forwardDom.status
    this.#backwardStatus = backwardDom.status
    this.seam = document.createElement('div')
    this.seam.className = 'vpa-fixed-side-seam'
    this.seam.title = 'Drag to resize; double-click to equalize'
    this.#declareButton = document.createElement('button')
    this.#declareButton.type = 'button'
    this.#declareButton.className = 'vpa-fixed-side-declare'
    this.seam.append(this.#declareButton)
    this.#narrowNotice = document.createElement('div')
    this.#narrowNotice.className = 'vpa-fixed-side-too-narrow'
    this.#narrowNotice.textContent = `Fixed-side proving requires a window at least ${MIN_FIXED_WORKSPACE_WIDTH}px wide. Widen the window to continue.`
    this.#narrowNotice.hidden = true
    this.root.append(forwardDom.pane, this.seam, backwardDom.pane, this.#narrowNotice)
    options.host.append(this.root)

    const model = (side: FixedSide) => ({
      side,
      diagram: () => currentSide(options.session(), side),
      boundary: () => sideBoundary(options.session(), side),
      context: options.context,
      theme: options.theme,
      fuel: options.fuel,
      apply: (step: ProofStep) => this.#apply(side, step),
      focused: () => this.#focused === side,
      focus: () => this.setFocusedSide(side),
      keyCommand: (sample: KeySample) => this.#keyCommand(side, sample),
      refuse: options.refuse,
      changed: options.changed,
    })
    this.forward = new ProofFrontViewport(forwardDom.canvas, model('forward'))
    this.backward = new ProofFrontViewport(backwardDom.canvas, model('backward'))
    this.#geometry = paneGeometry(window.innerWidth, window.innerHeight, this.#ratio, FIXED_SIDE_SEAM_WIDTH)

    this.seam.addEventListener('pointerdown', this.#seamDown)
    this.seam.addEventListener('pointermove', this.#seamMove)
    this.seam.addEventListener('pointerup', this.#seamUp)
    this.seam.addEventListener('pointercancel', this.#seamUp)
    this.seam.addEventListener('dblclick', this.#equalize)
    this.#declareButton.addEventListener('click', this.#declare)
    window.addEventListener('resize', this.#windowResize)
    this.#layout()
    this.#refresh()
  }

  get focusedSide(): FixedSide { return this.#focused }
  get ratio(): number { return this.#ratio }

  setFocusedSide(side: FixedSide): void {
    if (side === this.#focused) return
    this.#focused = side
    this.forward.setFocused(side === 'forward')
    this.backward.setFocused(side === 'backward')
    this.#options.focusChanged(side)
    this.#refresh()
  }

  reconcile(side: FixedSide): void {
    this.#front(side).reconcileDiagram()
    this.#refresh()
  }

  moveFocusedCursor(cursor: number): void {
    const next = moveSide(this.#options.session(), this.#focused, cursor)
    this.#options.commit(next, this.#focused)
    this.reconcile(this.#focused)
  }

  cancelGestures(): void {
    this.forward.cancelActiveGesture()
    this.backward.cancelActiveGesture()
  }

  frame(): void {
    if (this.#disposed) return
    this.#layout()
    this.forward.frame()
    this.backward.frame()
  }

  layout(): FixedSideGeometry {
    this.#layout()
    return this.#geometry
  }

  debugState(): FixedSideWorkspaceDebug {
    const session = this.#options.session()
    return {
      ratio: this.#ratio,
      focused: this.#focused,
      met: meet(session),
      forward: {
        ...this.forward.debugState(), cursor: session.forward.cursor,
        selected: this.forward.interaction.selection.length, pinCount: this.forward.interaction.pins.size,
      },
      backward: {
        ...this.backward.debugState(), cursor: session.backward.cursor,
        selected: this.backward.interaction.selection.length, pinCount: this.backward.interaction.pins.size,
      },
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.cancelGestures()
    this.seam.removeEventListener('pointerdown', this.#seamDown)
    this.seam.removeEventListener('pointermove', this.#seamMove)
    this.seam.removeEventListener('pointerup', this.#seamUp)
    this.seam.removeEventListener('pointercancel', this.#seamUp)
    this.seam.removeEventListener('dblclick', this.#equalize)
    this.#declareButton.removeEventListener('click', this.#declare)
    window.removeEventListener('resize', this.#windowResize)
    this.forward.dispose()
    this.backward.dispose()
    this.root.remove()
  }

  #front(side: FixedSide): ProofFrontViewport {
    return side === 'forward' ? this.forward : this.backward
  }

  #apply(side: FixedSide, step: ProofStep): void {
    const session = this.#options.session()
    const next = side === 'forward' ? applyForward(session, step) : applyBackward(session, step)
    this.#options.commit(next, side)
    this.reconcile(side)
  }

  #keyCommand(side: FixedSide, sample: KeySample): boolean {
    if (this.#focused !== side || !(sample.ctrlKey || sample.metaKey) || sample.key.toLowerCase() !== 'z') return false
    const session = this.#options.session()
    const timeline = session[side]
    const cursor = timeline.cursor + (sample.shiftKey ? 1 : -1)
    if (cursor < 0 || cursor >= timeline.states.length) {
      this.#options.refuse(`nothing to ${sample.shiftKey ? 'redo' : 'undo'} on the ${side} front`, {
        x: side === 'forward' ? window.innerWidth * 0.25 : window.innerWidth * 0.75,
        y: window.innerHeight * 0.5,
      })
      return true
    }
    this.#options.commit(moveSide(session, side, cursor), side)
    this.reconcile(side)
    return true
  }

  #refresh(): void {
    const session = this.#options.session()
    const isMet = meet(session)
    this.root.dataset.focused = this.#focused
    this.seam.classList.toggle('is-met', isMet)
    this.#declareButton.disabled = !isMet
    this.#declareButton.textContent = isMet ? 'MEET · DECLARE' : 'DISTINCT'
    this.#forwardStatus.value = `FORWARD · ${session.forward.cursor}/${session.forward.states.length - 1}`
    this.#backwardStatus.value = `BACKWARD · ${session.backward.cursor}/${session.backward.states.length - 1}`
    this.forward.setFocused(this.#focused === 'forward')
    this.backward.setFocused(this.#focused === 'backward')
    this.#options.changed()
  }

  #layout(): void {
    const tooNarrow = window.innerWidth < MIN_FIXED_WORKSPACE_WIDTH
    this.#narrowNotice.hidden = !tooNarrow
    if (tooNarrow) return
    const rect = this.root.getBoundingClientRect()
    const width = rect.width || window.innerWidth
    const height = rect.height || window.innerHeight
    const geometry = paneGeometry(width, height, this.#ratio, FIXED_SIDE_SEAM_WIDTH)
    this.#geometry = geometry
    this.#place(this.#forwardPane, geometry.forward)
    this.#place(this.seam, geometry.seam)
    this.#place(this.#backwardPane, geometry.backward)
    this.forward.resize(geometry.forward.width, geometry.forward.height)
    this.backward.resize(geometry.backward.width, geometry.backward.height)
  }

  #place(element: HTMLElement, rect: { x: number; y: number; width: number; height: number }): void {
    element.style.left = `${rect.x}px`
    element.style.top = `${rect.y}px`
    element.style.width = `${rect.width}px`
    element.style.height = `${rect.height}px`
  }

  #makePane(side: FixedSide): { pane: HTMLDivElement; canvas: HTMLCanvasElement; status: HTMLOutputElement } {
    const pane = document.createElement('div')
    pane.className = `vpa-proof-front vpa-proof-front-${side}`
    const status = document.createElement('output')
    status.className = 'vpa-proof-front-status'
    const canvas = document.createElement('canvas')
    canvas.className = 'vpa-proof-front-canvas'
    canvas.setAttribute('aria-label', `${side} proof front`)
    pane.append(status, canvas)
    return { pane, canvas, status }
  }

  #seamDown = (event: PointerEvent): void => {
    if (event.button !== 0 || event.target === this.#declareButton) return
    this.cancelGestures()
    this.#dragging = true
    this.seam.setPointerCapture(event.pointerId)
    this.#setRatioFromPointer(event)
  }

  #seamMove = (event: PointerEvent): void => {
    if (this.#dragging) this.#setRatioFromPointer(event)
  }

  #seamUp = (event: PointerEvent): void => {
    if (!this.#dragging) return
    this.#dragging = false
    if (this.seam.hasPointerCapture(event.pointerId)) this.seam.releasePointerCapture(event.pointerId)
  }

  #setRatioFromPointer(event: PointerEvent): void {
    const rect = this.root.getBoundingClientRect()
    this.#ratio = dividerRatioAt(event.clientX, rect.left, rect.width)
    this.#layout()
    this.#options.changed()
  }

  #equalize = (event: MouseEvent): void => {
    if (event.target === this.#declareButton) return
    this.#ratio = 0.5
    this.#layout()
    this.#options.changed()
  }

  #declare = (): void => {
    if (!meet(this.#options.session())) return
    this.#options.declare()
    this.#refresh()
  }

  #windowResize = (): void => {
    if (window.innerWidth < MIN_FIXED_WORKSPACE_WIDTH) this.cancelGestures()
    this.#layout()
  }
}
