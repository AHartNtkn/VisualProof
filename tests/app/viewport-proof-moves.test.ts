import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import {
  membraneCrossingHits,
  preparedMembrane,
  type Hit,
  type PreparedMembrane,
} from '../../src/app/hittest'
import { ProofMoveController } from '../../src/app/interact/moves'
import { InteractiveViewport } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../../src/kernel/diagram/diagram'
import { relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { carryOver, mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

class TestPointerEvent extends Event {
  readonly pointerId: number
  readonly button: number
  readonly clientX: number
  readonly clientY: number
  readonly shiftKey: boolean
  readonly ctrlKey: boolean
  readonly altKey: boolean
  readonly metaKey: boolean

  constructor(type: string, point: Vec2, pointerId = 1) {
    super(type, { bubbles: false, cancelable: true })
    this.pointerId = pointerId
    this.button = 0
    this.clientX = point.x
    this.clientY = point.y
    this.shiftKey = false
    this.ctrlKey = false
    this.altKey = false
    this.metaKey = false
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

function wrapNode(diagram: Diagram, node: NodeId): {
  readonly diagram: Diagram
  readonly outer: RegionId
} {
  const wrapped = applyDoubleCutIntro(diagram, mkSelection(diagram, {
    region: diagram.nodes[node]!.region,
    regions: [],
    nodes: [node],
    wires: [],
  }))
  const inner = wrapped.nodes[node]!.region
  const outerRegion = wrapped.regions[inner]
  if (outerRegion?.kind !== 'cut') throw new Error('wrapped node has no inner cut')
  return { diagram: wrapped, outer: outerRegion.parent }
}

function placeMembrane(
  engine: Engine,
  membrane: PreparedMembrane,
  center: Vec2,
): void {
  engine.regions.set(membrane.outer, {
    center,
    radius: 30,
    support: [],
  })
  engine.regions.set(membrane.inner, {
    center,
    radius: 18,
    support: [],
  })
  for (const node of membrane.selection.nodes) engine.bodies.get(node)!.pos = center
}

function membranePoint(engine: Engine, membrane: PreparedMembrane): Vec2 {
  const circle = engine.regions.get(membrane.outer)!
  return vec(circle.center.x, circle.center.y - circle.radius)
}

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
  let selection: readonly Hit[] = []
  const host = new TestHTMLElement(dom.document) as unknown as HTMLElement
  const moves = new ProofMoveController({
    host,
    active: () => true,
    diagram: () => currentDiagram,
    engine: () => currentEngine,
    viewScale: () => 1,
    selection: () => selection,
    setSelection: (next) => { selection = next },
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
  const viewport = new InteractiveViewport({
    canvas: canvas as unknown as HTMLCanvasElement,
    view: { scale: 1, offsetX: 0, offsetY: 0 },
    engine: () => currentEngine,
    diagram: () => currentDiagram,
    selectionEnabled: () => false,
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

function click(harness: GestureHarness, point: Vec2): void {
  pointer(harness, 'pointerdown', point)
  pointer(harness, 'pointerup', point)
}

function pressEscape(): TestKeyboardEvent {
  const event = new TestKeyboardEvent('Escape')
  dom.window.dispatchEvent(event)
  return event
}

function pendingFixture(count: number): {
  readonly harness: GestureHarness
  readonly membranes: readonly PreparedMembrane[]
} {
  const builder = new DiagramBuilder()
  const nodes = Array.from({ length: count }, () =>
    builder.ref(builder.root, 'NullaryBody', relSig([])))
  let diagram = builder.build()
  const outers: RegionId[] = []
  for (const node of nodes) {
    const wrapped = wrapNode(diagram, node)
    diagram = wrapped.diagram
    outers.push(wrapped.outer)
  }
  const membranes = outers.map((outer) => preparedMembrane(diagram, outer)!)
  const engine = mkEngine(diagram, [])
  membranes.forEach((membrane, index) =>
    placeMembrane(engine, membrane, vec(200 + 300 * index, 200)))
  return { harness: createHarness(diagram, engine), membranes }
}

function groundingFixture(
  orientation: 'forward' | 'backward' = 'forward',
): {
  readonly harness: GestureHarness
  readonly membrane: PreparedMembrane
  readonly relation: WireId
} {
  const builder = new DiagramBuilder()
  const negative = builder.cut(builder.root)
  const application = builder.atom(negative, relSig([]))
  const content = builder.ref(negative, 'NullaryBody', relSig([]))
  const relation = builder.wire(negative, [{
    node: application,
    port: { kind: 'head' },
  }], relSig([]))
  const wrapped = wrapNode(builder.build(), content)
  const membrane = preparedMembrane(wrapped.diagram, wrapped.outer)!
  const engine = mkEngine(wrapped.diagram, [])
  placeMembrane(engine, membrane, vec(300, 200))
  engine.bodies.get(application)!.pos = vec(100, 200)
  engine.bodies.get(`j:${relation}`)!.pos = vec(130, 200)
  return {
    harness: createHarness(wrapped.diagram, engine, orientation),
    membrane,
    relation,
  }
}

describe('Viewport → ProofMoveController cancellation', () => {
  it('cancels a fresh physical claim even when policy has no released state yet', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'UnaryBody', UNARY)
    const formal = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 0 },
    }])
    const wrapped = wrapNode(builder.build(), content)
    const membrane = preparedMembrane(wrapped.diagram, wrapped.outer)!
    const engine = mkEngine(wrapped.diagram, [])
    placeMembrane(engine, membrane, vec(300, 200))
    engine.bodies.get(`j:${formal}`)!.pos = vec(300, 310)
    const crossing = membraneCrossingHits(engine).find((hit) =>
      hit.key.membrane === membrane.outer && hit.key.wire === formal)!.at
    const harness = createHarness(wrapped.diagram, engine)

    pointer(harness, 'pointerdown', crossing)
    expect(harness.canvas.hasPointerCapture(1)).toBe(true)
    const escape = pressEscape()

    expect(escape.defaultPrevented).toBe(true)
    expect(harness.canvas.hasPointerCapture(1)).toBe(false)
    expect(() => pointer(harness, 'pointerup', crossing)).not.toThrow()
    expect(harness.moves.overlay()).toEqual([])
    expect(harness.actions).toEqual([])
  })

  it('makes pointer-up inert after Escape cancels an active grounding drag', () => {
    const { harness, membrane, relation } = groundingFixture()
    const source = harness.engine.bodies.get(`j:${relation}`)!.pos
    const target = membranePoint(harness.engine, membrane)
    pointer(harness, 'pointerdown', source)
    pointer(harness, 'pointermove', target)

    expect(harness.canvas.hasPointerCapture(1)).toBe(true)
    pressEscape()

    expect(harness.moves.overlay()).toEqual([])
    expect(harness.canvas.hasPointerCapture(1)).toBe(false)
    expect(() => pointer(harness, 'pointerup', target)).not.toThrow()
    expect(harness.actions).toEqual([])
  })

  it('makes pointer-up inert after Escape cancels an active branch drag', () => {
    const { harness, membranes } = pendingFixture(2)
    const first = membranePoint(harness.engine, membranes[0]!)
    click(harness, first)
    const body = vec(first.x, first.y - 22)
    const second = membranePoint(harness.engine, membranes[1]!)
    pointer(harness, 'pointerdown', body)
    pointer(harness, 'pointermove', second)

    expect(harness.canvas.hasPointerCapture(1)).toBe(true)
    pressEscape()

    expect(harness.moves.overlay()).toEqual([])
    expect(harness.canvas.hasPointerCapture(1)).toBe(false)
    expect(() => pointer(harness, 'pointerup', second)).not.toThrow()
    expect(harness.actions).toEqual([])
  })

  it('makes pointer-up inert after Escape cancels an active loose-end drag', () => {
    const { harness, membranes } = pendingFixture(1)
    const first = membranePoint(harness.engine, membranes[0]!)
    click(harness, first)
    const looseEnd = vec(first.x, first.y - 22 + 36)
    const scope = vec(400, 400)
    pointer(harness, 'pointerdown', looseEnd)
    pointer(harness, 'pointermove', scope)

    expect(harness.canvas.hasPointerCapture(1)).toBe(true)
    pressEscape()

    expect(harness.moves.overlay()).toEqual([])
    expect(harness.canvas.hasPointerCapture(1)).toBe(false)
    expect(() => pointer(harness, 'pointerup', scope)).not.toThrow()
    expect(harness.actions).toEqual([])
  })
})

describe('Viewport → ProofMoveController relation gestures', () => {
  it('commits successful grounding through the real viewport claim route', () => {
    const { harness, membrane, relation } = groundingFixture()
    const source = harness.engine.bodies.get(`j:${relation}`)!.pos
    const target = membranePoint(harness.engine, membrane)

    pointer(harness, 'pointerdown', source)
    pointer(harness, 'pointermove', target)
    pointer(harness, 'pointerup', target)

    expect(harness.actions).toHaveLength(1)
    expect(harness.actions[0]!.steps).toEqual([
      expect.objectContaining({
        rule: 'wireJoin',
        input: expect.objectContaining({
          kind: 'relation',
          wire: relation,
          parameters: [],
        }),
      }),
    ])
    expect(harness.refusals).toEqual([])
  })

  it('commits successful severing through membrane and loose-end viewport claims', () => {
    const { harness, membranes } = pendingFixture(1)
    const contact = membranePoint(harness.engine, membranes[0]!)
    click(harness, contact)
    const looseEnd = vec(contact.x, contact.y - 22 + 36)
    const scope = vec(400, 400)

    pointer(harness, 'pointerdown', looseEnd)
    pointer(harness, 'pointermove', scope)
    pointer(harness, 'pointerup', scope)

    expect(harness.actions).toHaveLength(1)
    expect(harness.actions[0]!.steps).toEqual([{
      rule: 'wireSever',
      input: {
        kind: 'relation',
        scope: harness.diagram.root,
        occurrences: [{
          sel: membranes[0]!.selection,
          args: [],
        }],
      },
    }])
    expect(harness.refusals).toEqual([])
  })

  it('routes ordinary kernel refusal without recording an action or changing the diagram', () => {
    const { harness, membrane, relation } = groundingFixture('backward')
    const before = harness.diagram
    const source = harness.engine.bodies.get(`j:${relation}`)!.pos
    const target = membranePoint(harness.engine, membrane)

    pointer(harness, 'pointerdown', source)
    pointer(harness, 'pointermove', target)
    pointer(harness, 'pointerup', target)

    expect(harness.actions).toEqual([])
    expect(harness.diagram).toBe(before)
    expect(harness.refusals.join('\n')).toMatch(
      /backward relation wire join requires a positive scope/,
    )
  })

  it('keeps pending overlay, hit, and sever commit attached to moved membrane layout', () => {
    const { harness, membranes } = pendingFixture(2)
    const originalFirst = membranePoint(harness.engine, membranes[0]!)
    click(harness, originalFirst)
    const oldBodyPoint = vec(originalFirst.x, originalFirst.y - 22)

    harness.engine.regions.set(membranes[0]!.outer, {
      center: vec(260, 260),
      radius: 40,
      support: [],
    })
    harness.engine.regions.set(membranes[0]!.inner, {
      center: vec(260, 260),
      radius: 24,
      support: [],
    })
    harness.engine.regions.set(membranes[1]!.outer, {
      center: vec(560, 260),
      radius: 35,
      support: [],
    })
    harness.engine.regions.set(membranes[1]!.inner, {
      center: vec(560, 260),
      radius: 20,
      support: [],
    })
    const movedBodyPoint = vec(260, 198)
    const movedSecond = vec(560, 225)
    const overlayCenters = harness.moves.overlay()
      .filter((shape) => shape.kind === 'circle')
      .map((shape) => shape.center)
    expect(overlayCenters).toContainEqual(movedBodyPoint)

    click(harness, oldBodyPoint)
    expect(harness.actions).toEqual([])
    pointer(harness, 'pointerdown', movedBodyPoint)
    pointer(harness, 'pointermove', movedSecond)
    pointer(harness, 'pointerup', movedSecond)

    const originalLooseEnd = vec(
      originalFirst.x,
      originalFirst.y - 22 + 36,
    )
    const scope = vec(700, 500)
    pointer(harness, 'pointerdown', originalLooseEnd)
    pointer(harness, 'pointermove', scope)
    pointer(harness, 'pointerup', scope)

    expect(harness.actions).toHaveLength(1)
    expect(harness.actions[0]!.steps[0]).toEqual({
      rule: 'wireSever',
      input: {
        kind: 'relation',
        scope: harness.diagram.root,
        occurrences: membranes.map((membrane) => ({
          sel: membrane.selection,
          args: [],
        })),
      },
    })
    expect(harness.refusals).toEqual([])
  })
})
