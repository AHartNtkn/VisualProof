import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { ProofMoveController } from '../../src/app/interact/moves'
import { InteractiveViewport } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { IOTA } from '../../src/kernel/diagram/sig'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { carryOver, mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'

class TestPointerEvent extends Event {
  readonly pointerId: number
  readonly button = 0
  readonly clientX: number
  readonly clientY: number
  readonly shiftKey = false
  readonly ctrlKey = false
  readonly altKey = false
  readonly metaKey = false

  constructor(type: string, point: Vec2, pointerId = 1) {
    super(type, { bubbles: false, cancelable: true })
    this.pointerId = pointerId
    this.clientX = point.x
    this.clientY = point.y
  }
}

class TestKeyboardEvent extends Event {
  readonly key: string
  readonly shiftKey = false
  readonly ctrlKey = false
  readonly altKey = false
  readonly metaKey = false
  readonly repeat = false

  constructor(key: string) {
    super('keydown', { bubbles: false, cancelable: true })
    this.key = key
  }
}

class TestCanvas extends EventTarget {
  readonly width = 800
  readonly height = 600
  tabIndex = 0
  readonly #captures = new Set<number>()

  focus(_options?: FocusOptions): void {}
  getBoundingClientRect(): DOMRect {
    return {
      x: 0,
      y: 0,
      left: 0,
      top: 0,
      right: this.width,
      bottom: this.height,
      width: this.width,
      height: this.height,
      toJSON: () => ({}),
    }
  }
  setPointerCapture(pointerId: number): void { this.#captures.add(pointerId) }
  hasPointerCapture(pointerId: number): boolean { return this.#captures.has(pointerId) }
  releasePointerCapture(pointerId: number): void { this.#captures.delete(pointerId) }
}

class TestHTMLElement extends EventTarget {
  readonly ownerDocument: Document
  readonly isContentEditable = false

  constructor(ownerDocument: Document) {
    super()
    this.ownerDocument = ownerDocument
  }
}

type TestDom = {
  readonly window: EventTarget
  readonly document: Document
}

type GestureHarness = {
  readonly canvas: TestCanvas
  readonly viewport: InteractiveViewport
  readonly moves: ProofMoveController
  readonly actions: ProofAction[]
  readonly refusals: string[]
  diagram: Diagram
  engine: Engine
}

const liveViewports: InteractiveViewport[] = []
let dom!: TestDom

beforeEach(() => {
  const windowTarget = new EventTarget()
  const documentTarget = Object.assign(new EventTarget(), {
    visibilityState: 'visible',
  }) as unknown as Document
  dom = { window: windowTarget, document: documentTarget }
  vi.stubGlobal('window', windowTarget)
  vi.stubGlobal('document', documentTarget)
  vi.stubGlobal('PointerEvent', TestPointerEvent)
  vi.stubGlobal('KeyboardEvent', TestKeyboardEvent)
  vi.stubGlobal('HTMLElement', TestHTMLElement)
  vi.stubGlobal('HTMLInputElement', class extends TestHTMLElement {})
  vi.stubGlobal('HTMLTextAreaElement', class extends TestHTMLElement {})
})

afterEach(() => {
  while (liveViewports.length > 0) liveViewports.pop()!.dispose()
  vi.unstubAllGlobals()
})

function createHarness(
  diagram: Diagram,
  engine: Engine,
  orientation: 'forward' | 'backward' = 'forward',
): GestureHarness {
  const canvas = new TestCanvas()
  const actions: ProofAction[] = []
  const refusals: string[] = []
  let currentDiagram = diagram
  let currentEngine = engine
  let viewport!: InteractiveViewport
  const host = new TestHTMLElement(dom.document) as unknown as HTMLElement
  const moves = new ProofMoveController({
    host,
    active: () => true,
    diagram: () => currentDiagram,
    engine: () => currentEngine,
    viewScale: () => 1,
    selection: () => viewport.selection,
    setSelection: (selection) => { viewport.setSelection(selection) },
    context: () => EMPTY_PROOF_CONTEXT,
    orientation: () => orientation,
    apply: (action) => {
      const previous = currentEngine
      currentDiagram = applyAction(
        currentDiagram,
        action,
        EMPTY_PROOF_CONTEXT,
        orientation,
      )
      actions.push(action)
      currentEngine = mkEngine(currentDiagram, [])
      carryOver(previous, currentEngine)
    },
    refuse: (text) => { refusals.push(text) },
    theme: () => LIGHT,
    fuel: () => 0,
    openSpawn: () => undefined,
  })
  viewport = new InteractiveViewport({
    canvas: canvas as unknown as HTMLCanvasElement,
    view: { scale: 1, offsetX: 0, offsetY: 0 },
    engine: () => currentEngine,
    diagram: () => currentDiagram,
    selectionEnabled: () => true,
    claim: (sample) => moves.claim(sample),
    doubleClick: (sample) => moves.doubleClick(sample),
    contextMenu: (sample) => { moves.contextMenu(sample) },
    pointerChanged: () => undefined,
    modifiersChanged: (ctrlHeld) => { moves.modifiersChanged(ctrlHeld) },
    keyDown: (sample) => moves.keyDown(sample),
    selectionChanged: () => undefined,
    selectionCommitted: () => undefined,
  })
  liveViewports.push(viewport)
  return {
    canvas,
    viewport,
    moves,
    actions,
    refusals,
    get diagram() { return currentDiagram },
    set diagram(next) { currentDiagram = next },
    get engine() { return currentEngine },
    set engine(next) { currentEngine = next },
  }
}

function pointer(
  harness: GestureHarness,
  type: 'pointerdown' | 'pointermove' | 'pointerup',
  point: Vec2,
): void {
  harness.canvas.dispatchEvent(new TestPointerEvent(type, point))
}

function drag(harness: GestureHarness, from: Vec2, to: Vec2): void {
  pointer(harness, 'pointerdown', from)
  pointer(harness, 'pointermove', to)
  pointer(harness, 'pointerup', to)
}

describe('Viewport → ProofMoveController wire connection', () => {
  it('preserves ordinary iota wire-to-wire dragging through the production route', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], IOTA)
    const right = builder.wire(negative, [], IOTA)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.regions.set(negative, {
      center: vec(300, 200),
      radius: 160,
      support: [],
    })
    engine.bodies.get(`j:${left}`)!.pos = vec(220, 200)
    engine.bodies.get(`j:${right}`)!.pos = vec(380, 200)
    const harness = createHarness(diagram, engine)

    drag(
      harness,
      engine.bodies.get(`j:${left}`)!.pos,
      engine.bodies.get(`j:${right}`)!.pos,
    )

    expect(harness.actions[0]?.steps[0]).toEqual({
      rule: 'wireJoin',
      input: { a: left, b: right },
    })
  })
})
