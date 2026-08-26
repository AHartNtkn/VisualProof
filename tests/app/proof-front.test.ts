import { afterEach, describe, expect, it, vi } from 'vitest'
import {
  frontInputAllowed,
  frontKeyRoute,
  retainedFrontIds,
} from '../../src/app/proof-front-policy'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { UNARY } from '../fixtures/zero-signature'
import { ProofFrontViewport } from '../../src/app/proof-front'
import { parseTerm } from '../../src/kernel/term/parse'
import { convertToWeakHeadNormal } from '../../src/app/tactics'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { defaultMotionPreferences } from '../../src/app/interact/motion'
import { LIGHT } from '../../src/view/paint'
import { REDEX_COLOR } from '../../src/view/lambda-motion'

class FrontDocument extends EventTarget {
  readonly body: FrontHost
  readonly visibilityState = 'visible'

  constructor() {
    super()
    this.body = new FrontHost(this as unknown as Document)
  }
}

class FrontHost extends EventTarget {
  constructor(readonly ownerDocument: Document) { super() }
  append(): void {}
}

class FrontCanvas extends EventTarget {
  width = 800
  height = 600
  readonly clientWidth = 800
  readonly clientHeight = 600
  tabIndex = 0
  readonly strokeColors: string[] = []
  readonly context = {
    clearRect: () => { this.strokeColors.length = 0 },
    fillRect: () => undefined,
    beginPath: () => undefined,
    roundRect: () => undefined,
    arc: () => undefined,
    fill: () => undefined,
    stroke: () => { this.strokeColors.push(this.context.strokeStyle) },
    moveTo: () => undefined,
    lineTo: () => undefined,
    bezierCurveTo: () => undefined,
    save: () => undefined,
    restore: () => undefined,
    measureText: () => ({ width: 1 }),
    fillText: () => undefined,
    createRadialGradient: () => ({ addColorStop: () => undefined }),
    fillStyle: '',
    strokeStyle: '',
    lineWidth: 1,
    lineJoin: 'round',
    lineCap: 'round',
    shadowBlur: 0,
    shadowColor: '',
    globalAlpha: 1,
    font: '',
    textAlign: 'center',
    textBaseline: 'middle',
  }

  getContext(): typeof this.context { return this.context }
  getBoundingClientRect(): DOMRect {
    return {
      x: 0, y: 0, left: 0, top: 0,
      right: this.width, bottom: this.height,
      width: this.width, height: this.height,
      toJSON: () => ({}),
    }
  }
  focus(): void {}
  closest(): null { return null }
  setPointerCapture(): void {}
  releasePointerCapture(): void {}
  hasPointerCapture(): boolean { return false }
}

afterEach(() => { vi.unstubAllGlobals() })

describe('proof-front policy', () => {
  it('routes input only to the focused, enabled front', () => {
    const key = {
      key: 'Home',
      shiftKey: false,
      ctrlKey: false,
      altKey: false,
      metaKey: false,
      repeat: false,
    }
    expect(frontKeyRoute(false, key)).toBeNull()
    expect(frontKeyRoute(true, key)).toBe(key)
    expect(frontInputAllowed(true, true)).toBe(true)
    expect(frontInputAllowed(true, false)).toBe(false)
  })

  it('drops selection and pin IDs absent from the current structural graph', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    expect(retainedFrontIds(
      diagram,
      [{ kind: 'node', id: node }, { kind: 'node', id: 'gone' }],
      [node, 'gone'],
    )).toEqual({
      selection: [{ kind: 'node', id: node }],
      pins: [node],
    })
  })

  it('paints and clears the sampled structural frame through the live 2D viewport', () => {
    const documentTarget = new FrontDocument()
    vi.stubGlobal('document', documentTarget)
    vi.stubGlobal('window', new EventTarget())
    vi.stubGlobal('HTMLElement', FrontHost)
    vi.stubGlobal('HTMLInputElement', class extends FrontHost {})
    vi.stubGlobal('HTMLTextAreaElement', class extends FrontHost {})

    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\x. x) a')
    const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
    let diagram = builder.build()
    const conversion = convertToWeakHeadNormal(diagram, node, 8)
    const canvas = new FrontCanvas()
    const viewport = new ProofFrontViewport(canvas as unknown as HTMLCanvasElement, {
      side: 'forward',
      diagram: () => diagram,
      boundary: () => [],
      context: () => EMPTY_PROOF_CONTEXT,
      theme: () => LIGHT,
      fuel: () => 8,
      prepare: () => () => undefined,
      prepareAction: () => () => undefined,
      motionPreferences: () => defaultMotionPreferences(false),
      workspaceInputAllowed: () => true,
      focused: () => true,
      focus: () => undefined,
      keyCommand: () => false,
      refuse: () => undefined,
      changed: () => undefined,
    })

    diagram = conversion.diagram
    viewport.reconcileDiagram({ label: 'beta', steps: [conversion.step], placements: [] })
    viewport.motion.scrubBeta(0.075)
    viewport.frame(100)
    expect(canvas.strokeColors).toContain(REDEX_COLOR)

    viewport.motion.settleBeta()
    viewport.frame(100)
    expect(canvas.strokeColors).not.toContain(REDEX_COLOR)
    viewport.dispose()
  })
})
