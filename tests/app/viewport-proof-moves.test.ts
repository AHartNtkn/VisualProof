import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import type { Hit } from '../../src/app/hittest'
import { ProofMoveController } from '../../src/app/interact/moves'
import { InteractiveViewport } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { carryOver, mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

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

function click(harness: GestureHarness, point: Vec2): void {
  pointer(harness, 'pointerdown', point)
  pointer(harness, 'pointerup', point)
}

function drag(harness: GestureHarness, from: Vec2, to: Vec2): void {
  pointer(harness, 'pointerdown', from)
  pointer(harness, 'pointermove', to)
  pointer(harness, 'pointerup', to)
}

function pressEscape(): TestKeyboardEvent {
  const event = new TestKeyboardEvent('Escape')
  dom.window.dispatchEvent(event)
  return event
}

function selectionIds(harness: GestureHarness): readonly Hit[] {
  return harness.viewport.selection
}

function pendingPoints(harness: GestureHarness): readonly Vec2[] {
  return harness.moves.overlay()
    .filter((shape) => shape.kind === 'circle')
    .map((shape) => shape.center)
}

function groundingFixture(
  arity: 0 | 1,
  orientation: 'forward' | 'backward' = 'forward',
): {
  readonly harness: GestureHarness
  readonly content: NodeId
  readonly formal: WireId | null
  readonly relation: WireId
} {
  const builder = new DiagramBuilder()
  const negative = builder.cut(builder.root)
  const sig = arity === 0 ? relSig([]) : UNARY
  const application = builder.atom(negative, sig)
  const content = builder.ref(negative, 'GroundBody', sig)
  const formal = arity === 0
    ? null
    : builder.wire(negative, [
        { node: application, port: { kind: 'arg', index: 0 } },
        { node: content, port: { kind: 'arg', index: 0 } },
      ])
  const relation = builder.wire(negative, [{
    node: application,
    port: { kind: 'head' },
  }], sig)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.regions.set(negative, {
    center: vec(300, 200),
    radius: 150,
    support: [],
  })
  engine.bodies.get(application)!.pos = vec(120, 200)
  engine.bodies.get(content)!.pos = vec(300, 200)
  engine.bodies.get(`j:${relation}`)!.pos = vec(80, 200)
  return {
    harness: createHarness(diagram, engine, orientation),
    content,
    formal,
    relation,
  }
}

function severFixture(count: number): {
  readonly harness: GestureHarness
  readonly scope: RegionId
  readonly nodes: readonly NodeId[]
  readonly points: readonly Vec2[]
} {
  const builder = new DiagramBuilder()
  const scope = builder.root
  const nodes = Array.from(
    { length: count },
    () => builder.ref(scope, 'NullaryBody', relSig([])),
  )
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  const points = nodes.map((node, index) => {
    const point = vec(230 + index * 180, 220)
    engine.bodies.get(node)!.pos = point
    return point
  })
  return {
    harness: createHarness(diagram, engine),
    scope,
    nodes,
    points,
  }
}

function nestedRegionSeverFixture(): {
  readonly harness: GestureHarness
  readonly scope: RegionId
  readonly extents: readonly [RegionId, RegionId]
  readonly points: readonly [Vec2, Vec2]
  readonly looseScopePoint: Vec2
} {
  const builder = new DiagramBuilder()
  const negative = builder.cut(builder.root)
  const scope = builder.cut(negative)
  const first = builder.cut(scope)
  const second = builder.cut(scope)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.regions.set(negative, {
    center: vec(400, 300),
    radius: 220,
    support: [],
  })
  engine.regions.set(scope, {
    center: vec(400, 300),
    radius: 170,
    support: [],
  })
  engine.regions.set(first, {
    center: vec(300, 230),
    radius: 45,
    support: [],
  })
  engine.regions.set(second, {
    center: vec(500, 230),
    radius: 45,
    support: [],
  })
  return {
    harness: createHarness(diagram, engine),
    scope,
    extents: [first, second],
    points: [vec(300, 230), vec(500, 230)],
    looseScopePoint: vec(400, 400),
  }
}

describe('Viewport → ProofMoveController ordered-selection gestures', () => {
  it('commits grounding from a prepared node selection without a diagram marker', () => {
    const { harness, content, relation } = groundingFixture(0)
    const contentPoint = harness.engine.bodies.get(content)!.pos
    const source = harness.engine.bodies.get(`j:${relation}`)!.pos

    click(harness, contentPoint)
    expect(selectionIds(harness)).toEqual([{ kind: 'node', id: content }])
    drag(harness, source, contentPoint)

    expect(harness.refusals).toEqual([])
    expect(harness.actions).toHaveLength(1)
    expect(harness.actions[0]?.steps[0]).toMatchObject({
      rule: 'wireJoin',
      input: {
        kind: 'relation',
        wire: relation,
        parameters: [],
        content: { boundary: [] },
      },
    })
    expect(selectionIds(harness)).toEqual([])
  })

  it('routes an invalid grounding through the kernel and keeps the selection', () => {
    const { harness, content, relation } = groundingFixture(1)
    const contentPoint = harness.engine.bodies.get(content)!.pos
    const source = harness.engine.bodies.get(`j:${relation}`)!.pos

    click(harness, contentPoint)
    drag(harness, source, contentPoint)

    expect(harness.actions).toEqual([])
    expect(harness.refusals).toHaveLength(1)
    expect(harness.refusals[0]).toMatch(
      /relation grounding boundary suffix has 0 positions; parameter count is 1/,
    )
    expect(selectionIds(harness)).toEqual([{ kind: 'node', id: content }])
  })

  it('founds, branches, and scopes one sever from separately prepared selections', () => {
    const { harness, scope, nodes, points } = severFixture(2)
    click(harness, points[0]!)
    drag(harness, points[0]!, vec(230, 340))
    expect(selectionIds(harness)).toEqual([])

    click(harness, points[1]!)
    const [body, loose] = [...pendingPoints(harness)]
      .sort((left, right) => left.y - right.y)
    drag(harness, body!, points[1]!)
    expect(selectionIds(harness)).toEqual([])

    const currentLoose = pendingPoints(harness)
      .find((point) => point.x === loose!.x && point.y === loose!.y)!
    drag(harness, currentLoose, vec(350, 400))

    expect(harness.refusals).toEqual([])
    expect(harness.actions).toHaveLength(1)
    expect(harness.actions[0]?.steps[0]).toMatchObject({
      rule: 'wireSever',
      input: {
        kind: 'relation',
        scope,
        occurrences: [
          { sel: { nodes: [nodes[0]] }, args: [] },
          { sel: { nodes: [nodes[1]] }, args: [] },
        ],
      },
    })
  })

  it('uses selected regions as contacts and the smallest containing region as sever scope', () => {
    const {
      harness,
      scope,
      extents,
      points,
      looseScopePoint,
    } = nestedRegionSeverFixture()

    click(harness, points[0])
    expect(selectionIds(harness)).toEqual([{ kind: 'region', id: extents[0] }])
    drag(harness, points[0], vec(300, 320))

    click(harness, points[1])
    const [body, loose] = [...pendingPoints(harness)]
      .sort((left, right) => left.y - right.y)
    drag(harness, body!, points[1])
    drag(harness, loose!, looseScopePoint)

    expect(harness.refusals).toEqual([])
    expect(harness.actions).toHaveLength(1)
    expect(harness.actions[0]?.steps[0]).toMatchObject({
      rule: 'wireSever',
      input: {
        kind: 'relation',
        scope,
        occurrences: [
          { sel: { region: scope, regions: [extents[0]] }, args: [] },
          { sel: { region: scope, regions: [extents[1]] }, args: [] },
        ],
      },
    })
  })

  it('Escape cancels grounding, pending-body, and pending-loose claims', () => {
    const ground = groundingFixture(0)
    const contentPoint = ground.harness.engine.bodies.get(ground.content)!.pos
    const source = ground.harness.engine.bodies.get(`j:${ground.relation}`)!.pos
    click(ground.harness, contentPoint)
    pointer(ground.harness, 'pointerdown', source)
    pointer(ground.harness, 'pointermove', contentPoint)
    expect(pressEscape().defaultPrevented).toBe(true)
    expect(() => pointer(ground.harness, 'pointerup', contentPoint)).not.toThrow()
    expect(ground.harness.actions).toEqual([])

    const sever = severFixture(2)
    click(sever.harness, sever.points[0]!)
    drag(sever.harness, sever.points[0]!, vec(230, 340))
    click(sever.harness, sever.points[1]!)
    const [body] = [...pendingPoints(sever.harness)]
      .sort((left, right) => left.y - right.y)
    pointer(sever.harness, 'pointerdown', body!)
    pointer(sever.harness, 'pointermove', sever.points[1]!)
    pressEscape()
    expect(() => pointer(sever.harness, 'pointerup', sever.points[1]!)).not.toThrow()
    expect(sever.harness.actions).toEqual([])

    const looseSever = severFixture(1)
    click(looseSever.harness, looseSever.points[0]!)
    drag(looseSever.harness, looseSever.points[0]!, vec(230, 340))
    const activeLoose = [...pendingPoints(looseSever.harness)]
      .sort((left, right) => right.y - left.y)[0]!
    pointer(looseSever.harness, 'pointerdown', activeLoose)
    pointer(looseSever.harness, 'pointermove', vec(350, 400))
    pressEscape()
    expect(() =>
      pointer(looseSever.harness, 'pointerup', vec(350, 400)),
    ).not.toThrow()
    expect(looseSever.harness.actions).toEqual([])
    expect(looseSever.harness.moves.overlay()).toEqual([])
  })

  it('keeps pending contact/body geometry attached to a moved selected node', () => {
    const { harness, nodes, points } = severFixture(2)
    click(harness, points[0]!)
    drag(harness, points[0]!, vec(230, 340))
    const oldBody = [...pendingPoints(harness)]
      .sort((left, right) => left.y - right.y)[0]!

    harness.engine.bodies.get(nodes[0]!)!.pos = vec(380, 180)
    const movedBody = pendingPoints(harness)
      .find((point) => point.x !== 230 || point.y !== 340)!

    expect(movedBody).not.toEqual(oldBody)
    click(harness, points[1]!)
    drag(harness, movedBody, points[1]!)
    expect(harness.refusals).toEqual([])
  })

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
      input: { kind: 'iota', a: left, b: right },
    })
  })
})
