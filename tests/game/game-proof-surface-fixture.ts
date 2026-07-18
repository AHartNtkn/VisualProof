import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import { GameProofViewport } from '../../src/game/interface/proof-surface'
import { gameProofMotionPreferences } from '../../src/game/interface/proof-motion'
import { mountTimelineLever } from '../../src/game/interface/timeline-lever'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'
import { DARK } from '../../src/view/paint'
import { comprehensionFixture } from '../app/comprehension-fixture'
import { minimalPuzzle } from './catalog-fixture'

const fixture = comprehensionFixture()
let diagram = fixture.diagram
let prepared = 0
let refusals = 0
let changed = 0
let timelineCursor = 3
const timelineRequests: number[] = []
const timelineStates = Array.from({ length: 8 }, () => diagram)
const host = document.querySelector<HTMLElement>('#host')!
const environment = mountLensEnvironment({
  host,
  substrateSeed: 'proof-surface-fixture',
  width: innerWidth,
  height: innerHeight,
})
const surface = new GameProofViewport({
  host: environment.proofCanvasSlot,
  overlayHost: environment.element,
  diagram: () => diagram,
  boundary: () => [],
  context: () => ({ theorems: new Map(), relations: new Map() }),
  orientation: () => 'forward',
  theme: () => DARK,
  fuel: () => 256,
  prepare: (step: ProofStep) => {
    prepared++
    const next = applyStep(diagram, step, { theorems: new Map(), relations: new Map() }, 'backward')
    return () => { diagram = next }
  },
  motionPreferences: () => gameProofMotionPreferences(true),
  inputAllowed: () => true,
  refuse: () => { refusals++ },
  changed: () => { changed++ },
})
const timeline = mountTimelineLever(
  environment.timelineHandleSlot,
  () => ({ states: timelineStates, steps: [], cursor: timelineCursor }),
  (cursor) => { timelineCursor = cursor; timelineRequests.push(cursor); timeline.refresh() },
)

const resize = (): void => {
  environment.setLayout(innerWidth, innerHeight)
  const rect = environment.proofCanvasSlot.getBoundingClientRect()
  surface.resize(rect.width, rect.height)
}
resize()

const worldToClient = (point: { readonly x: number; readonly y: number }) => {
  const rect = surface.canvas.getBoundingClientRect()
  return {
    x: rect.left + (point.x * surface.view.scale + surface.view.offsetX) * rect.width / surface.canvas.width,
    y: rect.top + (point.y * surface.view.scale + surface.view.offsetY) * rect.height / surface.canvas.height,
  }
}

const state = {
  mapping: (client: { readonly x: number; readonly y: number }) => surface.mapClient(client),
  proofNodePoint: () => worldToClient([...surface.engine.bodies.values()].find((body) => body.node !== null)!.pos),
  selection: () => surface.debug().selection.map((hit) => `${hit.kind}:${hit.id}`),
  clearSelection: (): void => surface.interaction.setSelection([]),
  selectParameter: (): void => surface.interaction.setSelection([{ kind: 'wire', id: fixture.parameter }]),
  open: (): boolean => surface.openConstruction(fixture.bubble, { x: innerWidth - 170, y: 170 }),
  construction: () => surface.debug().construction,
  editing: (): boolean => surface.editing,
  prepared: (): number => prepared,
  refusals: (): number => refusals,
  changed: (): number => changed,
  refuseIncompleteArtifact: (): void => { surface.dropArtifact(minimalPuzzle(), { x: 10, y: 10 }) },
  cornerAlpha: (): number => {
    surface.frame(performance.now())
    return surface.canvas.getContext('2d')!.getImageData(0, 0, 1, 1).data[3]!
  },
  timeline: () => ({ cursor: timelineCursor, requests: [...timelineRequests] }),
  setTimelineCursor: (cursor: number): void => { timelineCursor = cursor; timeline.refresh() },
  disposeAndProbe: () => {
    surface.dispose()
    const snapshot = () => ({
      callbacks: { prepared, refusals, changed },
      debug: surface.debug(),
      canvas: { width: surface.canvas.width, height: surface.canvas.height },
    })
    const before = snapshot()
    const opened = surface.openConstruction(fixture.bubble, { x: 100, y: 100 })
    const drop = surface.dropArtifact(minimalPuzzle(), { x: 100, y: 100 })
    surface.reconcileDiagram()
    surface.cancelActiveGesture()
    surface.resize(before.canvas.width + 200, before.canvas.height + 100)
    return { before, after: snapshot(), opened, drop }
  },
}

declare global { interface Window { __gameProofSurfaceFixture: typeof state } }
window.__gameProofSurfaceFixture = state

const animate = (now: number): void => { surface.frame(now); requestAnimationFrame(animate) }
requestAnimationFrame(animate)
