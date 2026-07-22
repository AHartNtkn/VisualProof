import { mountLensEnvironment } from '../../src/game/interface/lens-environment'
import { GameProofViewport } from '../../src/game/interface/proof-surface'
import { brushHitTest } from '../../src/interaction/hittest'
import { gameProofMotionPreferences } from '../../src/game/interface/proof-motion'
import { mountTimelineLever } from '../../src/game/interface/timeline-lever'
import { applyAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { DARK } from '../../src/view/paint'
import { dependentComprehensionFixture } from '../app/comprehension-fixture'
import { minimalPuzzle } from './catalog-fixture'

const fixture = dependentComprehensionFixture()
let diagram = fixture.diagram
let prepared = 0
const preparedSteps: ProofStep[] = []
let refusals = 0
let changed = 0
let timelineCursor = 3
const timelineRequests: number[] = []
const timelineStates = Array.from({ length: 8 }, () => diagram)
let layoutFrozen = false
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
  context: () => EMPTY_PROOF_CONTEXT,
  artifactAvailable: () => false,
  orientation: () => 'backward',
  theme: () => DARK,
  fuel: () => 256,
  prepare: (action) => {
    if ('kind' in action) throw new Error('fixture does not prepare artifact actions')
    prepared++
    preparedSteps.push(...action.steps)
    const next = applyAction(diagram, action, EMPTY_PROOF_CONTEXT, 'backward')
    return () => { diagram = next }
  },
  motionPreferences: () => gameProofMotionPreferences(true),
  inputAllowed: () => true,
  refuse: () => { refusals++ },
  changed: () => { changed++ },
})
const timeline = mountTimelineLever(
  environment.timelineHandleSlot,
  { kind: 'active', timeline: { states: timelineStates, actions: [], cursor: timelineCursor } },
  (cursor) => {
    timelineCursor = cursor
    timelineRequests.push(cursor)
    timeline.update({
      kind: 'active',
      timeline: { states: timelineStates, actions: [], cursor: timelineCursor },
    })
  },
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

const regionBoundaryPoint = (id: string) => {
  const region = surface.engine.regions.get(id)
  if (region === undefined) throw new Error(`region '${id}' has no rendered geometry`)
  for (const inset of [3, 5, 7, 9]) {
    for (let index = 0; index < 360; index += 1) {
      const angle = index * Math.PI / 180
      const point = {
        x: region.center.x + Math.cos(angle) * (region.radius - inset),
        y: region.center.y + Math.sin(angle) * (region.radius - inset),
      }
      const neighborhood = [
        point,
        { x: point.x - 0.75, y: point.y },
        { x: point.x + 0.75, y: point.y },
        { x: point.x, y: point.y - 0.75 },
        { x: point.x, y: point.y + 0.75 },
      ]
      if (neighborhood.every((sample) => {
        const hit = brushHitTest(
          surface.engine,
          sample,
          { scale: surface.view.scale },
          false,
        )
        return hit?.kind === 'region' && hit.id === id
      })) return worldToClient(point)
    }
  }
  throw new Error(`region '${id}' has no robust pointer-reachable boundary point`)
}

const cutBoundaryPoint = () => regionBoundaryPoint(fixture.guard)

const nodePoint = (id: string) => {
  const body = surface.engine.bodies.get(id)
  if (body === undefined) throw new Error(`node '${id}' has no rendered geometry`)
  return worldToClient(body.pos)
}

const rootTargetPoint = () => {
  const frame = surface.engine.frame
  if (frame === null) throw new Error('proof frame has no rendered geometry')
  const offsets = [
    { x: 0.82, y: 0.82 },
    { x: -0.82, y: 0.82 },
    { x: 0.82, y: -0.82 },
    { x: -0.82, y: -0.82 },
  ]
  for (const offset of offsets) {
    const point = {
      x: frame.center.x + frame.half * offset.x,
      y: frame.center.y + frame.half * offset.y,
    }
    const insideCut = [...surface.engine.regions.entries()].some(([id, region]) =>
      diagram.regions[id]?.kind !== 'sheet'
      && Math.hypot(point.x - region.center.x, point.y - region.center.y) <= region.radius)
    if (!insideCut) return worldToClient(point)
  }
  throw new Error('proof root has no pointer-reachable iteration target')
}

const guardCopies = (): number => Object.entries(diagram.regions)
  .filter(([, region]) => region.kind === 'cut' && region.parent === diagram.root)
  .filter(([cut]) => Object.entries(diagram.regions).some(([bubble, region]) =>
    region.kind === 'bubble'
    && region.parent === cut
    && Object.values(diagram.nodes).filter((node) =>
      node.kind === 'atom' && node.region === bubble).length === 2))
  .length

const state = {
  freezeLayout: (): void => { layoutFrozen = true },
  mapping: (client: { readonly x: number; readonly y: number }) => surface.mapClient(client),
  proofNodePoint: () => worldToClient([...surface.engine.bodies.values()].find((body) => body.node !== null)!.pos),
  proofNodePoints: () => [...surface.engine.bodies.values()]
    .filter((body) => body.node !== null)
    .slice(0, 2)
    .map((body) => worldToClient(body.pos)),
  dependentBubblePoint: () => regionBoundaryPoint(fixture.dependentBubble),
  dependentBubble: () => fixture.dependentBubble,
  hostAtomPoint: () => nodePoint(fixture.hostAtom),
  hostAtom: () => fixture.hostAtom,
  expectedHostBinder: () => fixture.outerBinder,
  voidPoint: () => rootTargetPoint(),
  cutIterationGesture: () => ({
    cut: fixture.guard,
    root: diagram.root,
    start: cutBoundaryPoint(),
    target: rootTargetPoint(),
  }),
  selectIterationCut: (): void => {
    surface.interaction.setSelection([{ kind: 'region', id: fixture.guard }])
  },
  iterationSnapshot: () => ({
    prepared,
    lastStep: preparedSteps.at(-1) ?? null,
    cutCopies: guardCopies(),
    regions: Object.keys(diagram.regions).length,
    nodes: Object.keys(diagram.nodes).length,
  }),
  selection: () => surface.debug().selection.map((hit) => `${hit.kind}:${hit.id}`),
  clearSelection: (): void => surface.interaction.setSelection([]),
  selectParameter: (): void => surface.interaction.setSelection([{ kind: 'wire', id: fixture.parameter }]),
  open: (): boolean => surface.openConstruction(fixture.dependentBubble, { x: 170, y: 170 }),
  construction: () => surface.debug().construction,
  lastPreparedStep: (): ProofStep | null => preparedSteps.at(-1) ?? null,
  editing: (): boolean => surface.editing,
  prepared: (): number => prepared,
  refusals: (): number => refusals,
  changed: (): number => changed,
  refuseIncompleteArtifact: (): void => {
    const artifact = minimalPuzzle()
    surface.dropArtifact({ id: artifact.id, diagram: artifact.goal.diagram }, { x: 10, y: 10 })
  },
  cornerAlpha: (): number => {
    surface.frame(performance.now())
    return surface.canvas.getContext('2d')!.getImageData(0, 0, 1, 1).data[3]!
  },
  timeline: () => ({ cursor: timelineCursor, requests: [...timelineRequests] }),
  setTimelineCursor: (cursor: number): void => {
    timelineCursor = cursor
    timeline.update({
      kind: 'active',
      timeline: { states: timelineStates, actions: [], cursor: timelineCursor },
    })
  },
  disposeAndProbe: () => {
    surface.dispose()
    const snapshot = () => ({
      callbacks: { prepared, refusals, changed },
      debug: surface.debug(),
      canvas: { width: surface.canvas.width, height: surface.canvas.height },
    })
    const before = snapshot()
    const opened = surface.openConstruction(fixture.dependentBubble, { x: 100, y: 100 })
    const artifact = minimalPuzzle()
    const drop = surface.dropArtifact({ id: artifact.id, diagram: artifact.goal.diagram }, { x: 100, y: 100 })
    surface.reconcileDiagram()
    surface.cancelActiveGesture()
    surface.resize(before.canvas.width + 200, before.canvas.height + 100)
    return { before, after: snapshot(), opened, drop }
  },
}

declare global { interface Window { __gameProofSurfaceFixture: typeof state } }
window.__gameProofSurfaceFixture = state

const animate = (now: number): void => {
  if (!layoutFrozen) surface.frame(now)
  requestAnimationFrame(animate)
}
requestAnimationFrame(animate)
